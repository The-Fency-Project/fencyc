use std::{collections::{HashMap, HashSet}, fs::File, io::{self, BufRead, BufReader}, mem};

use crate::{lexer::lexer::{Intrinsic, Kword, Tok, Token}, seman::seman::{FType, StructTable, ftype_to_idx}};

pub struct FcParser {
    tokens: Vec<Token>,
    pos: usize,
    line: usize, // not for all cases
    overload_ctr: HashMap<String, usize>,
    call_ctr: usize,
    allowed_tok: Option<Tok>, // additional tok allowed to appear and break parse 
                                // e.g. comma (further)
    prev_flags: HashSet<ParseFlags>,
    curmod: String, // cur module name
    funcs: FuncTable,
    pub structs: StructTable,
    nm_interner: NameInterner,
}

/// Parser based on Pratt parsing algorithm
impl FcParser {
    pub fn new(toks: Vec<Token>) -> FcParser {
        FcParser { 
            tokens: toks, 
            pos: 0, line: 0, 
            overload_ctr: HashMap::new(),
            call_ctr: 0,
            allowed_tok: None,
            prev_flags: HashSet::new(),
            curmod: "main".to_owned(),
            funcs: FuncTable::new(),
            structs: StructTable::new(),
            nm_interner: NameInterner { map: HashMap::new() }
        }
    }

    /// Returns AST (0) and Function table (1) with no function bodies
    pub fn parse_everything(&mut self) -> (Vec<AstRoot>, FuncTable) {
        let mut ast: Vec<AstRoot> = Vec::new();

        while self.peek().is_some() {
            let expr = self.parse_expr(0);

            ast.push(expr);
        }

        (ast, self.funcs.clone())
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
            Tok::Double(fv) => AstNode::Double(*fv),
            Tok::strlit(s) => AstNode::StringLiteral(s.to_owned()),
            Tok::I32(iwv) => AstNode::I32(*iwv),
            Tok::Single(sv) => AstNode::Single(*sv),
            Tok::U32(uwv) => AstNode::U32(*uwv),
            Tok::Ibyte(ibv) => AstNode::Ibyte(*ibv),
            Tok::Ubyte(ubv) => AstNode::Ubyte(*ubv),

            Tok::Keyword(Kword::True) => AstNode::boolVal(true),
            Tok::Keyword(Kword::False) => AstNode::boolVal(false),
            Tok::Keyword(Kword::Module) => {
                let name = self.expect_idt().unwrap_or("".to_owned());

                if name.is_empty() {
                    // TODO: put here error into astnode 
                    println!("{}: expected module name", self.line);
                    return AstNode::Invalid;
                }

                let old_mod = self.curmod.clone();
                self.curmod = match old_mod.as_str() {
                    "main" => name.clone(),
                    other => format!("{}::{}", other, name),
                };
                let node = self.parse_expr(0);
                self.curmod = old_mod;

                AstNode::Module {
                    name: name,
                    node: Box::new(node)
                }
            }

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
                if let Some(t) = self.peek() {
                    if t.tok == Tok::DollarSign {
                        self.consume();
                        let typename = self.expect_idt().unwrap_or_else(|| {
                            panic!("{}: expected typename", self.line);
                        }); 
                        let tgt_ftype = match_ftype(&typename, &mut self.nm_interner)
                            .unwrap_or_else(|| {
                            panic!("{}: unknown type {}", self.line, &typename);
});

                        return AstNode::ExprCast { 
                            expr: Box::new(expr.node), 
                            target_type: tgt_ftype 
                        };
                    }
                };
                expr.node
            },

            Tok::Plus => self.parse_expr(255).node,

            Tok::Exclam => AstNode::UnaryOp { 
                op: UnaryOp::LogicalNot, 
                expr: Box::new(self.parse_expr(255).node) 
            },

            Tok::LBr => {
                let mut vals: Vec<AstNode> = Vec::new();
                self.allowed_tok = Some(Tok::Comma);
                while let Some(t) = self.peek() {
                    if t.tok == Tok::RBr {
                        self.consume();
                        break;
                    }
                    if t.tok == Tok::At {
                        self.consume();
                        let count = self.expect_uint();
                        vals.push(AstNode::ArrRep(count.1));
                        self.consume();
                        break;
                    }
                    vals.push(self.parse_expr(0).node);
                };
                self.allowed_tok = None;
                let typename = self.expect_idt().unwrap_or_else(|| {
                    panic!("{}: expected typename after array end (e.g. [1, 2]int)", self.line);
                }); 
                let ft = match_ftype(&typename, &mut self.nm_interner)
                    .unwrap_or(FType::none);

                AstNode::Array(ft, vals)
            }

            Tok::Identifier(idt) => {
                let idt_cl                            = idt.clone();
                let mut el_idx: Option<Box<AstRoot>>  = None;
                let mut buf: Vec<AstNode>             = Vec::new();

                while let Some(nexttok) = self.peek() {
                    match &nexttok.tok.clone() {
                        Tok::Semicol => {
                            break;
                        }
                        Tok::Equals => {
                            self.consume();
                            let nameval = Box::new(buf.get(0).cloned()
                                    .unwrap_or(AstNode::Variable(idt_cl)));
                            return AstNode::Reassignment { 
                                name: nameval, 
                                idx: el_idx,
                                newval: Box::new(self.parse_expr(0))
                            }
                        }
                        Tok::Combined(tok1, tok2) => {
                            match (tok1.as_ref(), tok2.as_ref()) {
                                (Tok::Colon, Tok::Colon) => {
                                    let path = self.parse_path(idt.clone());
                                    
                                    if self.peek_is(Tok::LPar) {
                                        return self.parse_call(&path);
                                    } else if self.peek_is(Tok::LCurBr) {
                                        return self.parse_struct_create(&path);
                                    }
                                }
                                (_, Tok::Equals) => {
                                    self.consume(); 
                                    let bop = self.match_bop_for_tok(&tok1, None)
                                        .unwrap_or_else(|| {
                                        panic!("{}: cant get binary op for operand {:?}", 
                                            self.line, tok1)
                                    });
                                    let right = self.parse_expr(0);
                                    let new_val_node = AstNode::BinaryOp { 
                                        op: bop, 
                                        left: Box::new(AstNode::Variable(idt_cl.clone())), 
                                        right: Box::new(right.node) 
                                    };
                                    return AstNode::Reassignment { 
                                        name: Box::new(AstNode::Variable(idt_cl)),
                                        idx: el_idx,
                                        newval: Box::new(
                                            AstRoot::new(new_val_node, self.line)
                                        )
                                    };
                                }
                                _ => {break;}
                            }
                        }
                        Tok::DollarSign => { // variable cast
                            self.consume();
                            let type_token = self.consume().unwrap_or_else(|| {
                                panic!("\n{}: expected typename for {}", line_n, idt);
                            });
                            let type_idt = match &type_token.tok {
                                Tok::Identifier(i) => i.clone(),
                                other => {
                                    panic!("\n{}: expected typename, found {:?}", 
                                        line_n, other);
                                }
                            };

                            let ftype = match_ftype(&type_idt, &mut self.nm_interner)
                                .unwrap_or_else(|| {
                                panic!("\n{}: {} is invalid type", line_n, type_idt);
                            });

                            return AstNode::VariableCast {
                                name: idt.to_owned(), 
                                target_type: ftype, 
                            }
                        }
                        Tok::LPar => { // function call
                            let name = AstNode::string_to_path(idt);

                            return self.parse_call(&name); 
                        }
                        Tok::LBr => {
                            self.consume();
                            self.allowed_tok = Some(Tok::RBr);
                            let idx_ast = self.parse_expr(0);
                            self.allowed_tok = None;
                            self.expect(Tok::RBr);
                            el_idx = Some(Box::new(idx_ast.clone()));

                            let n = AstNode::ArrayElem(idt.clone(), Box::new(idx_ast));
                            buf.push(n);
                        }
                        Tok::LCurBr => {
                            let path = self.parse_path(idt_cl.clone()).clone();
                            let n = self.parse_struct_create(&path);
                            buf.push(n);
                        }
                        Tok::Dot => {
                            self.consume();
                            let field_name = self.expect_idt()
                                .expect(&format!("{}: expected field name", self.line));
                            buf.push(AstNode::StructFieldAddr { 
                                var_name: idt.clone(), 
                                field_name 
                            });
                        }
                        other => {break;}
                    }
                }

                match buf.get(0) {
                    Some(ast_r) => {return ast_r.clone();},
                    None => {
                        return AstNode::Variable(idt.clone());
                    }
                }
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

            Tok::Keyword(Kword::Pub) => {
                self.prev_flags.insert(ParseFlags::Public);
                let expr = self.parse_expr(0);
                self.prev_flags.remove(&ParseFlags::Public);
                expr.node
            }

            Tok::Keyword(Kword::Func) => {
                let f = self.parse_func(false);
                self.funcs.push_func(FuncDat::new_from_astn(&f.0)
                    .expect(&format!("{}: Expected func", self.line)));
                self.overload_ctr.insert(f.1, 0);
                f.0
            }
            Tok::Keyword(Kword::Extern) => {
                self.consume();
                let f = self.parse_func(true);
                self.funcs.push_func(FuncDat::new_from_astn(&f.0)
                    .expect(&format!("{}: Expected func", self.line)));
                self.overload_ctr.insert(f.1, 0);
                f.0
            }

            Tok::Keyword(Kword::Overload) => {
                self.consume();
                let f = self.parse_func(false);
                self.funcs.push_func(FuncDat::new_from_astn(&f.0)
                    .expect(&format!("{}: Expected func", self.line)));
                let idx = {
                    let h = self.overload_ctr.get_mut(&f.1).unwrap();
                    *h += 1;
                    *h
                };
                
                AstNode::FunctionOverload { 
                    func: Box::new(f.0),
                    idx: idx,
                    public: self.prev_flags.contains(&ParseFlags::Public) 
                }
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
                            name: Box::new(AstNode::Variable(var_name)),
                            idx: None,
                            newval: Box::new(AstRoot::new(new_val_node, line))
                        } 
                    },
                    _ => {
                        panic!("{}: unknown op Compound({:?},{:?})", line, tok1, tok2)
                    }
                }
            }

            Tok::Keyword(Kword::Struct) => {
                let res = self.parse_struct();
                self.structs.push_from_astn(&res);
                res
            }

            other => {
                if Some(other) == self.allowed_tok.as_ref() {
                    return self.parse_expr(255).node;
                }
                panic!("{}: FCparse unexpected token `{:?}`", line_n, other);
            }
        }
    }

    fn parse_ftype_assignm(&mut self) -> FType {
        let mut ftype = FType::none;

        let ftype_tok = match self.consume() {
            Some(v) => {
                let cl = v.clone();
                match &cl.tok {
                    Tok::Identifier(idt) => {
                        if idt.starts_with("s_") {
                            return self.parse_path_type(idt.to_owned(), 2); 
                        } 
                    }
                    Tok::Star => {
                        let idt = self.expect_idt().expect(&format!(
                            "{}: expected typename after asterrisk",
                            self.line
                        ));
                        return self.parse_path_type(
                            format!("ptr_{}", idt), 
                            4
                        ); 
                    }
                    other => {
                    }
                }
                cl
            },
            None => {
                return ftype;
            }
        };
        let ftype_name = match &ftype_tok.tok {
            Tok::Identifier(nm) => nm,
            Tok::LBr => {
                let ftn = self.expect_idt();
                if let Some(name) = ftn {
                    self.expect(Tok::RBr);
                    let ft = match_ftype(&name, &mut self.nm_interner)
                        .unwrap_or_else(|| {panic!("{}: unknown type {}", self.line, name)});
                    ftype = FType::Array(ftype_to_idx(&ft), 0, 0);
                } 
                return ftype;
            }
            _ => {
                    return ftype;
                }
            };
        if let Some(ft) = match_ftype(&ftype_name, &mut self.nm_interner) {
            ftype = ft;
        };

        ftype
    }

    fn parse_path_type(&mut self, idt: String, idx: usize) -> FType {
        let mut ftype = FType::none;

        let parsed = self.parse_path(idt.clone());
        let mut st = parsed.path_to_string();
        let path = match st.contains("::") {
            true => st,
            false => {
                st.insert_str(idx, 
                    &format!("{}::", self.curmod)
                );
                st
            }
        };
        if let Some(ft) = match_ftype(&path, 
            &mut self.nm_interner) {
            ftype = ft;
        };
        return ftype;
    }

    fn parse_path(&mut self, first: String) -> AstNode {
        let mut segments = match first.contains("::") {
            true => first
                .split("::")
                .map(|s| s.to_owned())
                .collect(),
            false => vec![first]
        };

        while let Some(tok) = self.peek() {
            match &tok.tok {
                Tok::Combined(t1, t2)
                    if matches!((t1.as_ref(), t2.as_ref()), (Tok::Colon, Tok::Colon)) =>
                {
                    self.consume(); 
                    let next = self.expect_idt()
                        .expect("Expected identifier after ::");
                    segments.push(next);
                }
                _ => break,
            }
        }

        AstNode::Path { segments }
    }

    fn parse_call(&mut self, idt: &AstNode) -> AstNode {
        let args_nodes = self.parse_args_call();
        self.call_ctr += 1;
        
        let name = match idt.path_to_string().contains("::") {
            true => idt.clone(),
            false => AstNode::string_to_path(&format!(
                "{}::{}", self.curmod, idt.path_to_string()
            ))
        };

        return AstNode::Call { 
            func_name: Box::new(name), 
            args: args_nodes,
            idx: self.call_ctr - 1,
        };
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

    fn expect_uint(&mut self) -> (Token, u64) {
        let line = self.line;
        if let Some(t) = self.consume() {
            let val: u64 = match &t.tok {
                Tok::Uint(uv) => *uv,
                other => {panic!("{}: expected uint, found {:?}", line, other);}
            };
            return (t.clone(), val);
        } else {
            panic!("unexpected EOF at {}", self.line);
        }
    }

    fn peek_prev_nth(&self, minus_n: usize) -> &Token {
        self.tokens.get(self.pos.saturating_sub(minus_n)).unwrap()
    }

    fn peek_is(&self, tok: Tok) -> bool {
        if let Some(v) = self.peek() {
            return v.tok == tok;
        } 
        false
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

    fn parse_func(&mut self, externed: bool) -> (AstNode, String) {
        let name_start = self.expect_idt().unwrap_or_else(|| {
            panic!("{}: Expected function name", self.line)
        });
        let name_start_mod = format!("{}::{}", self.curmod, name_start);

        let name = self.parse_path(name_start_mod); 

        let args = self.parse_func_args();

        let ret_type = self.parse_func_rettype();

        if !externed {
            let body = self.parse_expr(0);

            (AstNode::Function { 
                name: Box::new(name.clone()), 
                args: args, 
                ret_type: ret_type, 
                body: Box::new(body.node),
                public: self.prev_flags.contains(&ParseFlags::Public) 
            }, name.path_to_string())
        } else {
            (AstNode::ExternedFunc { 
                name: Box::new(name.clone()),
                args: args, 
                ret_type: ret_type,
                public: self.prev_flags.contains(&ParseFlags::Public),
                real_name: Box::new(AstNode::string_to_path(&name_start)),
            }, name.path_to_string())
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

            let arg_name = self.expect_idt().unwrap_or_else(|| {
                panic!("{}: expected arg name", self.line)}
            );
            self.expect(Tok::Colon);
            if let Some(v) = self.peek() {
                if v.tok == Tok::LBr {
                    self.consume();
                    let arg_typename = self.expect_idt().unwrap_or_else(|| {
                        panic!("{}: expected typename for arg", self.line)}
                    );
                    let el_ft = match_ftype(&arg_typename, &mut self.nm_interner)
                        .unwrap_or_else(|| {
                        panic!("{}: unknown type {}", self.line, arg_typename)}
                    );
                    let ft = FType::Array(ftype_to_idx(&el_ft), 0, 0);

                    res.push(FuncArg::new(arg_name, ft));
                    self.expect(Tok::RBr);
                    continue;
                }
            };

            let mut is_ptr = false;
            if self.peek_is(Tok::Star) {
                self.consume();
                is_ptr = true;
            }

            let arg_typename_start = self.expect_idt().unwrap_or_else(|| {
                panic!("{}: expected typename for arg", self.line)}
            );

            let arg_typename = match (arg_typename_start.starts_with("s_"), is_ptr) {
                (true, false) => {
                    let path_start = arg_typename_start;
                    let path = self.parse_path(path_start);
                    format!("{}", path
                        .prep_module_at(&self.curmod, 2)
                        .path_to_string())
                } 
                (false, true) => {
                    let path = self.parse_path(arg_typename_start);
                    format!("ptr_{}", path
                        .prep_module_at(&self.curmod, 0)
                        .path_to_string())
                }
                (false, false) => {
                    arg_typename_start
                }
                (true, true) => {
                    unreachable!()
                }
            };

            let ft = match_ftype(&arg_typename, &mut self.nm_interner)
                .unwrap_or_else(|| {
                panic!("{}: unknown type {}", self.line, arg_typename)}
            );

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

            match_ftype(&ftype_name, &mut self.nm_interner)
                .unwrap_or_else(|| 
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

    fn parse_struct(&mut self) -> AstNode {
        let name_start = self.expect_idt().unwrap_or_else(|| {
            panic!("{}: Expected function name", self.line)
        });
        let name_start_mod = format!("{}::{}", self.curmod, name_start);

        let name = self.parse_path(name_start_mod);

        let fields = self.parse_struct_fields();

        AstNode::Structure { 
            name: Box::new(name), 
            fields: fields 
        }
    }

    fn parse_struct_fields(&mut self) -> Vec<AstNode> {
        let mut res: Vec<AstNode> = Vec::new();

        self.expect(Tok::LCurBr);
        loop {
            let line = self.line;
            let nexttok = self.consume()
                .expect(&format!("{}: Expected struct field", line))
                .clone();

            match &nexttok.tok {
                Tok::RCurBr => {
                    break;
                }
                Tok::Identifier(idt) => {
                    self.expect(Tok::Colon);
                    let typename = self.expect_idt()
                        .expect(&format!("{}: expected tyypename", line));
                    let ft = match_ftype(&typename, &mut self.nm_interner)
                        .expect(&format!("{}: unknown type {}", line, typename));
                    res.push(AstNode::StructField { 
                        name: idt.clone(), 
                        ftype: ft
                    });
                }
                other => panic!("{}: unexpected {:?}", line, other)
            }
        }

        res
    }

    pub fn parse_struct_create(&mut self, path: &AstNode) -> AstNode {
        let mut st = path.path_to_string();
        let fin_path = match st.contains("::") {
            true => path.clone(),
            false => {
                st.insert_str(0, &format!("{}::", self.curmod));
                AstNode::string_to_path(&st)
            }
        };

        self.expect(Tok::LCurBr);
        let fieldvals = self.parse_field_vals();

        AstNode::StructCreate { 
            name: Box::new(fin_path), 
            field_vals: fieldvals 
        }
    }

    fn parse_field_vals(&mut self) -> HashMap<String, Box<AstNode>> {
        let mut res = HashMap::new();
        
        loop {
            if self.peek_is(Tok::RCurBr) {
                self.consume();
                break;
            }    

            let name = self.expect_idt().expect(
                &format!("{}: expected field name", self.line)
            );

            self.expect(Tok::Colon);

            let val = self.parse_expr(0).node;

            res.insert(name, Box::new(val));
        }

        res
    }
}

#[derive(Debug, Clone)]
pub enum AstNode {
    none,
    NoParse, // internal astnode to stop parsing expr
    Invalid, // invalid node

    Int(i64),
    Double(f64),
    Uint(u64),
    I32(i32),
    Single(f32),
    U32(u32),
    Ibyte(i8),
    Ubyte(u8),
    boolVal(bool),
    StringLiteral(String),
    Variable(String),
    Array(FType, Vec<AstNode>),
    ArrayElem(String, Box<AstRoot>), // arrname, idx val
    ArrRep(u64), // repeat array elems N times

    CodeBlock {
        exprs: Vec<AstRoot>,
    },

    Path {
        segments: Vec<String>
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
        name: Box<AstNode>, // astnode::path
        args: Vec<FuncArg>,
        ret_type: FType,
        body: Box<AstNode>,
        public: bool,
    },

    ExternedFunc {
        name: Box<AstNode>,
        real_name: Box<AstNode>, 
        args: Vec<FuncArg>,
        ret_type: FType,
        public: bool,
    },

    FunctionOverload {
        func: Box<AstNode>,
        idx: usize, 
        public: bool,
    },

    ReturnVal {
        val: Box<AstRoot>,
    },

    Call {
        func_name: Box<AstNode>,
        args: Vec<AstRoot>,
        idx: usize, // call id
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
        name: Box<AstNode>,
        idx: Option<Box<AstRoot>>,
        newval: Box<AstRoot>,
    },

    VariableCast {
        name: String,
        target_type: FType
    },

    ExprCast {
        expr: Box<AstNode>,
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
   
    Module {
        name: String,
        node: Box<AstRoot>
    },


    Structure {
        name: Box<AstNode>, // astnode path 
        fields: Vec<AstNode>,

    },

    StructField {
        name: String,
        ftype: FType,
    },

    StructCreate {
        name: Box<AstNode>, // astnode::path 
        field_vals: HashMap<String, Box<AstNode>>,
    },

    StructFieldAddr {
        var_name: String,
        field_name: String,
    },
}

impl AstNode {
    /// Get path segments, 
    /// panic if its not a path node.
    pub fn path_to_segs(&self) -> Vec<String> {
        match self {
            AstNode::Path { segments } => {
                segments.clone()
            }
            other => panic!("Expected Path node, got {:?}", other)
        }
    }

    /// Joins path into one string, with :: sep
    pub fn path_to_string(&self) -> String {
        let segs = self.path_to_segs();
        segs.join("::")
    }

    pub fn segs_to_path(segs: &Vec<String>) -> AstNode {
        AstNode::Path { segments: segs.clone() }
    }

    pub fn string_to_path(st: &str) -> AstNode {
        let segs: Vec<String> = st.
            split("::")
            .map(|s| s.to_owned())
            .collect();
        AstNode::segs_to_path(&segs)
    }

    pub fn prep_module_at(&self, module: &str, idx: usize) -> AstNode {
        let mut st = self.path_to_string();
        match st.contains("::") {
            true => {},
            false => {
                st.insert_str(idx, 
                    &format!("{}::", module)
                ); 
            }
        }
        Self::string_to_path(&st)
    }
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

#[derive(Debug, Clone, PartialEq, Copy, Eq, Hash)]
pub enum ParseFlags {
    Public,
}

/// for more memory efficiency
struct NameInterner {
    map: HashMap<String, &'static str>,
}

impl NameInterner {
    fn intern(&mut self, s: &str) -> &'static str {
        if let Some(&existing) = self.map.get(s) {
            return existing;
        }
        let static_ref = Box::leak(s.to_owned().into_boxed_str());
        self.map.insert(s.to_owned(), static_ref);
        static_ref
    }
}

pub fn match_ftype(lit: &str, interner: &mut NameInterner) -> Option<FType> {
    match lit {
        "uint" => Some(FType::uint),
        "int" => Some(FType::int),
        "double" => Some(FType::double),
        "bool" => Some(FType::bool),
        "str" => Some(FType::strconst),
        "single" => Some(FType::single),
        "u32" => Some(FType::u32),
        "i32" => Some(FType::i32),
        "ubyte" => Some(FType::ubyte),
        "ibyte" => Some(FType::ibyte),
        other if lit.starts_with("s_") => Some(
            FType::Struct(interner.intern(&lit[2..]))
        ),
        other if lit.starts_with("ptr_") => Some(
            FType::StructPtr(interner.intern(&lit[4..]))
        ),
        other => None,
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

#[derive(Debug, Clone)]
pub struct FuncDat {
    pub name: AstNode,
    pub args: Vec<FuncArg>,
    pub ret_type: FType,
    pub externed: bool,
    pub public: bool,
    pub real_name: Option<String>,
}

impl FuncDat {
    pub fn new(nm: AstNode, ar: Vec<FuncArg>, ret: FType, ext: bool) -> FuncDat {
        FuncDat { 
            name: nm, 
            args: ar, 
            ret_type: ret,
            externed: ext,
            public: false,
            real_name: None,
        }
    }

    pub fn new_from_astn(node: &AstNode) -> Option<FuncDat> {
        let res = match node {
            AstNode::Function { name, args, ret_type, body, public } => {
                let mut fdat = FuncDat::new(
                    *name.clone(), args.clone(), *ret_type, false
                );
                fdat.public = *public;
                Some(fdat)
            }
            AstNode::FunctionOverload { func, idx, public } => {
                let mut fdat = Self::new_from_astn(&func).unwrap();
                fdat.public = fdat.public || *public;
                Some(fdat)
            }
            AstNode::ExternedFunc { name, args, ret_type, public, real_name } => {
                let mut fdat = FuncDat::new(
                    *name.clone(), args.clone(), *ret_type, false
                );
                fdat.public = *public;
                fdat.real_name = Some(real_name.path_to_string());
                Some(fdat)
            }
            _ => None,
        };
        res
    }
}

#[derive(Debug, Clone)]
pub struct FuncTable {
    // function name
    ft: HashMap<String, Vec<FuncDat>>
}

impl FuncTable {
    pub fn new() -> FuncTable {
        FuncTable { ft: HashMap::new() }
    }

    pub fn from_several(fts: &mut Vec<FuncTable>) -> FuncTable {
        let mut ft = FuncTable::new();

        for v in fts.drain(..) {
            ft.ft.extend(v.ft);
        }

        ft
    }

    pub fn push_func(&mut self, fndat: FuncDat) {
        if let Some(f) = self.ft.get_mut(&fndat.name.path_to_string()) {
            f.push(fndat);
        } else {
            self.ft.insert(
                fndat.name.path_to_string(),
                vec![fndat]
            );
        }
    }

    pub fn get_func(&mut self, name: &str) -> Option<&Vec<FuncDat>> {
        self.ft.get(name)
    }
}
