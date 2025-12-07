use std::{fs::File, io::{self, BufRead, BufReader}};

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

    pub fn parse_everything(&mut self) -> Vec<AstRoot> {
        let mut res: Vec<AstRoot> = Vec::new();
        while self.peek().is_some() {
            let expr = self.parse_expr(0);
            res.push(expr);
        }
        res
    }

    fn parse_block(&mut self) -> Vec<AstRoot> {
        self.expect(Tok::LCurBr);
        let mut res: Vec<AstRoot> = Vec::new();
        
        while let Some(tok) = self.peek() {
            if tok.tok == Tok::RCurBr {
                self.consume();
                break;
            }
            let astr = self.parse_expr(0);
            res.push(astr);
        }

        res
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

            Tok::LCurBr => AstNode::EnterScope, 
            Tok::RCurBr => AstNode::LeftScope,

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

                self.expect(Tok::Colon);
                let ftype_tok = self.consume()
                    .expect(&format!("{}: expected type annotation", line_n)
);
                let ftype_name = match &ftype_tok.tok {
                    Tok::Identifier(nm) => nm,
                    other => {
                        panic!("{}: Expected typename, found {:?}", line_n, other);
                    }
                };
                let ftype = match_ftype(&ftype_name)
                    .expect(
                        &format!("{}: unknown type", line_n)
                    );
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

            other => {
                panic!("{}: FCparse unexpected token `{:?}`", line_n, other);
            }
        }
    }

    fn expect(&mut self, want: Tok) {
        match self.consume() {
            Some(t) if t.tok == want => {},
            Some(t) => panic!("{}: expected {:?}, got {:?}", t.line, want, t.tok),
            None => panic!("expected {:?}, found EOF", want),
        }
    }

    /// Pratt binding powers: (left_bp, right_bp)
    fn infix_binding_power(tok: &Tok) -> Option<(u8, u8)> {
        match tok {
            Tok::DLAngBr => Some((8, 9)),
            Tok::DRAngBr => Some((8, 9)),
            Tok::Plus | Tok::Minus => Some((10, 11)),
            Tok::Star | Tok::Slash => Some((20, 21)),
            Tok::Equals => Some((3, 4)),
            Tok::VerBar => Some((8, 9)),
            Tok::Caret => Some((10, 11)),
            Tok::Ampersand => Some((12, 13)),
            _ => None,
        }
    }

    fn consume(&mut self) -> Option<&Token> {
        let tok = self.tokens.get(self.pos); 
        self.pos += 1;                      
        tok
    }

    fn expect_consume(&mut self, want: Tok) -> Option<&Token> {
        self.expect(want);
        self.consume()
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn parse_if(&mut self) -> AstNode {
        let condition = self.parse_expr(0); 

        let iftrue = self.parse_block();
        let iffalse: Option<Vec<AstRoot>> = match self.peek() {
            None => None,
            Some(token) => {
                if token.tok == Tok::Keyword(Kword::Else) {
                    self.consume();
                    Some(self.parse_block())
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
            Tok::Keyword(Kword::Let) => Some(BinaryOp::Assignment),
            Tok::Ampersand => Some(BinaryOp::BitwiseAnd),
            Tok::VerBar => Some(BinaryOp::BitwiseOr),
            Tok::Caret => Some(BinaryOp::BitwiseXor),
            Tok::DLAngBr => {
                return Some(BinaryOp::BitShiftLeft);
            }
            Tok::DRAngBr => {
                return Some(BinaryOp::BitShiftRight);
            }
            _ => {
                None
            },
        }
    }


}

#[derive(Debug, Clone)]
pub enum AstNode {
    Int(i64),
    Float(f64),
    Uint(u64),
    boolVal(bool),
    StringLiteral(String),
    Variable(String),
    Identifier(String),

    EnterScope,
    LeftScope,

    BinaryOp {
        op: BinaryOp,
        left: Box<AstNode>,
        right: Box<AstNode>,
    },

    UnaryOp {
        op: UnaryOp,
        expr: Box<AstNode>,
    },

    Call {
        func: Box<AstNode>,
        args: Vec<AstNode>,
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
        if_true: Vec<AstRoot>,
        if_false: Option<Vec<AstRoot>>
    },
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum BinaryOp {
    Add, 
    Substract,
    Multiply,
    Divide,
    Assignment,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    BitShiftRight,
    BitShiftLeft,
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum UnaryOp {
    Negate, 
    Not,
    LogicalNot,
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

