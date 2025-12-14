use std::{collections::HashMap, fs::File, io::{self, BufRead, BufReader}};

use crate::{lexer::lexer::{Intrinsic, Kword, Tok, Token}, seman::seman::FType};

pub struct FcParser {
    tokens: Vec<Token>,
    pos: usize,
    line: usize, // not for all cases
}

/// Parser based on Pratt parsing algorithm
impl FcParser {
    pub fn new(toks: Vec<Token>) -> FcParser {
        FcParser { tokens: toks, pos: 0, line: 0 }
    }

    /// Returns AST (0) and Function table (1) with no function bodies
    pub fn parse_everything(&mut self) -> (Vec<AstRoot>, HashMap<String, (AstNode, FType)>) {
        let mut ast: Vec<AstRoot> = Vec::new();
        let mut funcs: HashMap<String, (AstNode, FType)> = HashMap::new();

        while self.peek().is_some() {
            let expr = self.parse_expr(0);

            if let AstNode::Function { name, args, ret_type, body } = &expr.node {
                funcs.insert(name.clone(), (AstNode::Function { 
                    name: name.clone(), 
                    args: args.clone(),
                    ret_type: *ret_type, 
                    body: Box::new(AstNode::none) 
                }, *ret_type));
            }

            ast.push(expr);
        }

        (ast, funcs)
    }

    pub fn parse_expr(&mut self, min_bp: u8) -> AstRoot {
        let mut left = self.parse_prefix();
        let mut line_n: usize = self.line;

        while let Some(tok) = self.peek() {
            line_n = tok.line;
            let optok = &tok.tok.clone();

            if *optok == Tok::Semicol {
                self.consume();
                break;
            }
    
            let (lbp, rbp) = match Self::infix_binding_power(optok) {
                Some(v) => v,
                None => break,
            };  

            if lbp <= min_bp {
                break;
            }

            let _ = self.consume(); 

            let right = self.parse_expr(rbp);
       
            let nexttok: Option<Tok> = match self.peek() {
                None => None,
                Some(v) => Some(v.tok.clone()),
            };

            left = AstNode::BinaryOp {
                op: self.match_bop_for_tok(optok, nexttok.as_ref()).unwrap(),
                left: Box::new(left),
                right: Box::new(right.node),
            };
    } 

        AstRoot::new(left, line_n)
    }

    fn parse_prefix(&mut self) -> AstNode {
        let token: &Token = &self.consume().expect("unexpected EOF").clone();
        let line_n: usize = token.line;
        self.line = line_n;

        match &token.tok {
            Tok::Int(iv) => AstNode::Int(*iv),
            Tok::Uint(uv) => AstNode::Uint(*uv),
            Tok::Float(fv) => AstNode::Float(*fv),

            Tok::Keyword(Kword::True) => AstNode::boolVal(true),
            Tok::Keyword(Kword::False) => AstNode::boolVal(false),

            Tok::LCurBr => {
                let mut exprs: Vec<AstRoot> = Vec::new();
                while let Some(t) = self.peek() {
                    if t.tok == Tok::RCurBr {
                        self.consume();
                        break;
                    }
                    exprs.push(self.parse_expr(0));
                }

                AstNode::CodeBlock { exprs: exprs }
            }

            Tok::Minus => AstNode::UnaryOp {
                op: UnaryOp::Negate,
                expr: Box::new(self.parse_expr(255).node),
            },

            Tok::Tilde => AstNode::UnaryOp { 
                op: UnaryOp::Not, 
                expr: Box::new(self.parse_expr(255).node) 
            },

            Tok::LPar => {
                let expr = self.parse_expr(0);
                self.expect(Tok::RPar);
                expr.node
            },

            Tok::Plus => self.parse_expr(255).node,

            Tok::Exclam => AstNode::UnaryOp { 
                op: UnaryOp::LogicalNot, 
                expr: Box::new(self.parse_expr(255).node) 
            },

            Tok::Identifier(idt) => {
                let idt_cl = idt.clone();
                if let Some(nexttok) = self.peek() {
                    if nexttok.tok == Tok::Equals {
                        self.consume();
                        return AstNode::Reassignment { 
                            name: idt_cl, 
                            newval: Box::new(self.parse_expr(0))
                        }
                    } else if let Tok::Combined(tok1, tok2) = &nexttok.tok.clone() {
                        if **tok2 == Tok::Equals {
                            self.consume(); 
                            let bop = self.match_bop_for_tok(tok1, None).unwrap_or_else(|| {
                                panic!("{}: cant get binary op for operand {:?}", self.line, tok1)
                            });
                            let right = self.parse_expr(0);
                            let new_val_node = AstNode::BinaryOp { 
                                op: bop, 
                                left: Box::new(AstNode::Variable(idt_cl.clone())), 
                                right: Box::new(right.node) 
                            };
                            return AstNode::Reassignment { 
                                name: idt_cl, 
                                newval: Box::new(AstRoot::new(new_val_node, self.line))
                            };
                        }
                    } else if nexttok.tok == Tok::DollarSign {
                        self.consume();
                        let type_token = self.consume().unwrap_or_else(|| {
                            panic!("\n{}: expected typename for {}", line_n, idt);
                        });
                        let type_idt = match &type_token.tok {
                            Tok::Identifier(i) => i,
                            other => {
                                panic!("\n{}: expected typename, found {:?}", line_n, other);
                            }
                        };

                        let ftype = match_ftype(&type_idt).unwrap_or_else(|| {
                            panic!("\n{}: {} is invalid type", line_n, type_idt);
                        });

                        return AstNode::VariableCast {
                            name: idt.to_owned(), 
                            target_type: ftype, 
                        }
                    } else if nexttok.tok == Tok::LPar {
                        let args_nodes = self.parse_args_call();

                        return AstNode::Call { 
                            func_name: idt.clone(), 
                            args: args_nodes 
                        };
                    }
                }
                AstNode::Variable(idt.clone())
            },
            Tok::Keyword(Kword::If) => self.parse_if(),

            Tok::Keyword(Kword::Let) => {
                let idt_tok = self.consume()
                    .expect(&format!("{}: expected identifier", line_n));
                let idt = match &idt_tok.tok {
                    Tok::Identifier(name) => name.clone(),
                    other => {
                        panic!("{}: Expected identifier, found {:?}", line_n, other);
                    }
                };
                
                let mut ftype = FType::none;
                if let Some(t) = self.peek() {
                    if t.tok == Tok::Colon {
                        self.consume();
                        ftype = match self.parse_ftype_assignm() {
                            FType::none => panic!("{}: typename is incorrect", self.line),
                            other => other
                        };
                    } else if t.tok == Tok::Equals { 
                    } else {
                        panic!("{}: expected type annotation or equals after identifier, found {:?}", self.line, t.tok);
                    }
                }
                self.expect(Tok::Equals);
                
                let expr = self.parse_expr(0);

                AstNode::Assignment { 
                    name: idt.clone(), 
                    val: Box::new(expr.node), 
                    ft: ftype 
                }
            }

            Tok::Intrin(intr) => {
                let val = self.parse_expr(0);

                AstNode::Intrinsic { intr: *intr, val: Box::new(val.node) }
            }

            Tok::Keyword(Kword::While) => {
                self.parse_whileloop()
            }

            Tok::Keyword(Kword::For) => {
                self.parse_forloop()
            }

            Tok::Keyword(Kword::Break) => {
                AstNode::BreakLoop
            }

            Tok::Keyword(Kword::Continue) => {
                AstNode::ContinueLoop
            }

            Tok::Keyword(Kword::Func) => {
                self.parse_func()
            }

            Tok::Keyword(Kword::Return) => {
                if let Some(t) = self.peek() {
                    if t.tok == Tok::Semicol {
                        return AstNode::ReturnVal { val: Box::new(AstRoot 
                            { node: AstNode::none, line: self.line }) 
                        };
                    }
                }

                let body = self.parse_expr(0);

                AstNode::ReturnVal { val: Box::new(body) }
            }

            Tok::Combined(tok1, tok2) => {
                let line = self.line;
                match (*tok1.clone(), *tok2.clone()) {
                    (_, Tok::Equals) => {
                        let var_name = match &self.peek_prev_nth(2).tok {
                            Tok::Identifier(idt) => idt.clone(),
                            other => panic!("{}: compound assignment left hand has to be identifier, not {:?}",
                                line, other)
                        };

                        let bp = FcParser::infix_binding_power(tok1).unwrap_or_else(|| {
                            panic!("Internal error at {}: no bp", self.line)
                        });

                        let sec = self.parse_expr(bp.1);
                        let bop = self.match_bop_for_tok(&tok1, None).unwrap_or_else(|| {
                            panic!("{}: cant get binary op for operand {:?}", line, tok1)
                        });
                        let new_val_node = AstNode::BinaryOp { 
                            op: bop, 
                            left: Box::new(AstNode::Variable(var_name.clone())), 
                            right: Box::new(sec.node) 
                        };

                        AstNode::Reassignment { 
                            name: var_name, 
                            newval: Box::new(AstRoot::new(new_val_node, line))
                        } 
                    },
                    _ => {
                        panic!("{}: unknown op Compound({:?},{:?})", line, tok1, tok2)
                    }
                }
            }

            other => {
                panic!("{}: FCparse unexpected token `{:?}`", line_n, other);
            }
        }
    }

    fn parse_ftype_assignm(&mut self) -> FType {
        let mut ftype = FType::none;

        let ftype_tok = match self.consume() {
            Some(v) => v,
            None => {return ftype;}
        };
        let ftype_name = match &ftype_tok.tok {
            Tok::Identifier(nm) => nm,
            _ => {
                    return ftype;
                }
            };
        if let Some(ft) = match_ftype(&ftype_name) {
            ftype = ft;
        };

        ftype
    }

    fn parse_args_call(&mut self) -> Vec<AstRoot> {
        let mut res: Vec<AstRoot> = Vec::new();

        self.expect(Tok::LPar);
        while let Some(t) = self.peek() {
            if t.tok == Tok::RPar {
                self.consume();
                break;
            }
            if res.len() > 0 {
                self.expect(Tok::Comma);
            }

            let newval = self.parse_expr(0);

            res.push(newval);
        };

        res
    }

    fn expect(&mut self, want: Tok) -> &Token {
        match self.consume() {
            Some(t) if t.tok == want => {t},
            Some(t) => panic!("{}: expected {:?}, got {:?}", t.line, want, t.tok),
            None => panic!("expected {:?}, found EOF", want),
        }
    }

    fn peek_prev_nth(&self, minus_n: usize) -> &Token {
        self.tokens.get(self.pos.saturating_sub(minus_n)).unwrap()
    }

    /// Pratt binding powers: (left_bp, right_bp)
    fn infix_binding_power(tok: &Tok) -> Option<(u8, u8)> {
        match tok {
            Tok::DLAngBr => Some((8, 9)),
            Tok::DRAngBr => Some((8, 9)),
            Tok::Plus | Tok::Minus => Some((10, 11)),
            Tok::Star | Tok::Slash | Tok::Percent => Some((20, 21)),
            Tok::Equals => Some((3, 4)),
            Tok::VerBar => Some((8, 9)),
            Tok::Caret => Some((10, 11)),
            Tok::Ampersand => Some((12, 13)),

            Tok::DoubleEq | Tok::RABEq | Tok::LABEq | Tok::ExclEq 
            | Tok::LAngBr | Tok::RAngBr => Some((8, 9)),
            _ => None,
        }
    }

    fn consume(&mut self) -> Option<&Token> {
        let tok = self.tokens.get(self.pos); 
        self.pos += 1;                      
        tok
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn parse_if(&mut self) -> AstNode {
        let condition = self.parse_expr(0); 

        let iftrue = Box::new(self.parse_expr(0));
        let iffalse: Option<Box<AstRoot>> = match self.peek() {
            None => None,
            Some(token) => {
                if token.tok == Tok::Keyword(Kword::Else) {
                    self.consume();
                    Some(Box::new(self.parse_expr(0)))
                } else {
                    None
                }
            }
        };        

        AstNode::IfStatement { 
            cond: Box::new(condition), 
            if_true: iftrue, 
            if_false: iffalse 
        }
    }

    

    pub fn match_bop_for_tok(&mut self, tok: &Tok, next_tok: Option<&Tok>) -> Option<BinaryOp> {
        match tok {
            Tok::Plus => Some(BinaryOp::Add),
            Tok::Minus => Some(BinaryOp::Substract),
            Tok::Star => Some(BinaryOp::Multiply),
            Tok::Slash => Some(BinaryOp::Divide),
            Tok::Percent => Some(BinaryOp::Remainder),

            Tok::Keyword(Kword::Let) => Some(BinaryOp::Assignment),
            Tok::Ampersand => Some(BinaryOp::BitwiseAnd),
            Tok::VerBar => Some(BinaryOp::BitwiseOr),
            Tok::Caret => Some(BinaryOp::BitwiseXor),
            Tok::DLAngBr => {
                return Some(BinaryOp::BitShiftLeft);
            }
            Tok::DRAngBr => {
                return Some(BinaryOp::BitShiftRight);
            },

            Tok::DoubleEq => {
                return Some(BinaryOp::Compare(CmpOp::Eq));
            },
            Tok::RABEq => {
                Some(BinaryOp::Compare(CmpOp::Ge))
            }
            Tok::RAngBr => {
                Some(BinaryOp::Compare(CmpOp::G))
            }
            Tok::LAngBr => {
                Some(BinaryOp::Compare(CmpOp::L))
            }
            Tok::ExclEq => {
                Some(BinaryOp::Compare(CmpOp::Ne))
            }
            Tok::LABEq => {
                Some(BinaryOp::Compare(CmpOp::Le))
            }

            _ => {
                return None;
            },
        }
    }

    fn parse_whileloop(&mut self) -> AstNode {
        let condition = self.parse_expr(0);

        let body = self.parse_expr(0);

        AstNode::WhileLoop { 
            cond: Box::new(condition), 
            body: Box::new(body) 
        }
    }

    fn parse_forloop(&mut self) -> AstNode {
        let itervar = self.parse_expr(0);

        self.expect(Tok::Keyword(Kword::In)); 

        let iter_cond = self.parse_expr(0);
        let iter_upd = self.parse_expr(0);

        let body = self.parse_expr(0);

        AstNode::ForLoop { 
            itervar: Box::new(itervar), 
            iter_upd: Box::new(iter_upd), 
            iter_cond: Box::new(iter_cond),
            body: Box::new(body) 
        }
    }

    fn parse_func(&mut self) -> AstNode {
        let name = self.expect_idt().unwrap_or_else(|| {
            panic!("{}: expected function name identifier", self.line)
        }); 

        let args = self.parse_func_args();

        let ret_type = self.parse_func_rettype();

        let body = self.parse_expr(0);

        AstNode::Function { 
            name: name, 
            args: args, 
            ret_type: ret_type, 
            body: Box::new(body.node)
        }
    }

    fn parse_func_args(&mut self) -> Vec<FuncArg> {
        let mut res: Vec<FuncArg> = Vec::new();
        
        self.expect(Tok::LPar);

        while let Some(token) = self.peek() {
            if token.tok == Tok::RPar {
                self.consume();
                break;
            }

            if res.len() > 0 {
                self.expect(Tok::Comma);
            }

            let arg_name = self.expect_idt().unwrap_or_else(|| {panic!("{}: expected arg name", self.line)});
            self.expect(Tok::Colon);
            let arg_typename = self.expect_idt().unwrap_or_else(|| {panic!("{}: expected typename for arg", self.line)});
            let ft = match_ftype(&arg_typename).unwrap_or_else(|| {panic!("{}: unknown type {}", self.line, arg_typename)});

            res.push(FuncArg::new(arg_name, ft));
        };

        res
    }

    fn parse_func_rettype(&mut self) -> FType {
        if let Some(t) = self.peek() {
            if t.tok != Tok::Combined(Box::new(Tok::Minus), Box::new(Tok::RAngBr)) {
                return FType::none;
            }

            self.consume();
            let ftype_name = self.expect_idt().unwrap_or_else( ||
                {panic!("{}: expected typename for return type", self.line);}
            );

            match_ftype(&ftype_name).unwrap_or_else(|| 
                {panic!("{}: invalid typename {}", self.line, &ftype_name);}
            )
        } else {
            panic!("{}: unexpected EOF while parsing return type", self.line);
        }
    }

    fn expect_idt(&mut self) -> Option<String> {
        match self.consume() {
            Some(t) => match &t.tok {
                Tok::Identifier(idt) => Some(idt.clone()),
                _ => None, //panic!("{}: expected function name identifier, found {:?}", self.line, t)
            },
            None => None //panic!("{}: expected function name identifier, found None", self.line)
        }   
    }
}

#[derive(Debug, Clone)]
pub enum AstNode {
    none, 

    Int(i64),
    Float(f64),
    Uint(u64),
    boolVal(bool),
    StringLiteral(String),
    Variable(String),
    Identifier(String),

    CodeBlock {
        exprs: Vec<AstRoot>,
    },

    BinaryOp {
        op: BinaryOp,
        left: Box<AstNode>,
        right: Box<AstNode>,
    },

    UnaryOp {
        op: UnaryOp,
        expr: Box<AstNode>,
    },

    Function {
        name: String,
        args: Vec<FuncArg>,
        ret_type: FType,
        body: Box<AstNode>,
    },

    ReturnVal {
        val: Box<AstRoot>,
    },

    Call {
        func_name: String,
        args: Vec<AstRoot>,
    },

    Intrinsic {
        intr: Intrinsic,
        val: Box<AstNode>,
    },

    Assignment {
        name: String,
        val: Box<AstNode>,
        ft: FType, 
    },

    Reassignment {
        name: String,
        newval: Box<AstRoot>
    },

    VariableCast {
        name: String,
        target_type: FType
    },

    IfStatement {
        cond: Box<AstRoot>,
        if_true: Box<AstRoot>,
        if_false: Option<Box<AstRoot>>
    },

    BreakLoop,
    ContinueLoop,

    WhileLoop {
        cond: Box<AstRoot>,
        body: Box<AstRoot>,
    },

    ForLoop {
        itervar: Box<AstRoot>,
        iter_upd: Box<AstRoot>, // e.g. a = a + 1 
        iter_cond: Box<AstRoot>, // e.g. a < 10
        body: Box<AstRoot>,
    },
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum BinaryOp {
    Add, 
    Substract,
    Multiply,
    Divide,
    Remainder,
    Assignment,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    BitShiftRight,
    BitShiftLeft,
    Compare(CmpOp),
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum UnaryOp {
    Negate, 
    Not,
    LogicalNot,
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum CmpOp {
    Eq, // ==
    Ge, // >=
    G, // >
    L, // <
    Le, // <=
    Ne, // !=
}

pub fn match_ftype(lit: &str) -> Option<FType> {
    match lit {
        "uint" => Some(FType::uint),
        "int" => Some(FType::int),
        "float" => Some(FType::float),
        "bool" => Some(FType::bool),
        other => None,
        // TODO: add support for objects and str
    }
}


#[derive(Debug, Clone)]
pub struct AstRoot {
    pub node: AstNode,
    pub line: usize 
}

impl AstRoot {
    pub fn new(node: AstNode, line: usize) -> AstRoot {
        AstRoot { node: node, line: line }
    }
}

#[derive(Debug, Clone)]
pub struct FuncArg {
    pub name: String, 
    pub ftype: FType
}

impl FuncArg {
    pub fn new(n: String, ft: FType) -> FuncArg {
        FuncArg { 
            name: n, 
            ftype: ft 
        }
    }
}
