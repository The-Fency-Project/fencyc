use std::{collections::{HashMap, HashSet}, io::BufRead};

use clap::ValueEnum;

use crate::{cli::Target, lexer::lexer::{Intrinsic, Kword, Tok, Token}, logger::logger::{ErrKind, LogLevel}, seman::seman::{FType, StructTable}};

macro_rules! unwrap_or_invalid {
    ($opt:expr, $parser:expr) => {
        match $opt {
            Some(v) => v,
            None => {
                return AstNode::Invalid(LogLevel::Error(
                    ErrKind::ParseExpectedIdt(
                        $parser
                            .peek()
                            .map_or(Tok::EOF, |t| t.tok.clone())
                    )
                ));
            }
        }
    };
}

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
    pub funcs: FuncTable,
    pub structs: StructTable,
    nm_interner: NameInterner,
    generics: Vec<GenericType>,
    pub traits: TraitTable,
    pub trait_impls: HashMap<String, HashSet<String>>, // struct name -> traits
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
            nm_interner: NameInterner { map: HashMap::new() },
            generics: Vec::new(),
            traits: TraitTable::new(),
            trait_impls: HashMap::new(),
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

        let mut res = AstRoot::new(left, line_n);
        let attr_to_remove = self.prev_flags
            .iter()
            .find(|flag| matches!(flag, ParseFlags::Attrs(_)))
            .cloned(); 
        if let Some(ParseFlags::Attrs(mut attrs)) = attr_to_remove {
            if !attrs.is_empty() && res.node.can_have_attrs() {
                self.prev_flags.remove(&ParseFlags::Attrs(attrs.clone()));
                res.attrs.extend(attrs.drain(..));
            }
        }
        res
    }

    const PREFIX_BP: u8 = 22;
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
                    let found = self.peek().map_or(Tok::EOF, |t| t.tok.clone());
                    return AstNode::Invalid(LogLevel::Error(
                            ErrKind::ParseExpectedIdt(found)
                            )
                        );
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
                expr: Box::new(self.parse_expr(Self::PREFIX_BP).node),
            },

            Tok::Tilde => AstNode::UnaryOp { 
                op: UnaryOp::Not, 
                expr: Box::new(self.parse_expr(Self::PREFIX_BP).node) 
            },

            Tok::Ampersand => AstNode::UnaryOp { 
                op: UnaryOp::AddressOf, 
                expr: Box::new(self.parse_expr(Self::PREFIX_BP).node) 
            },

            Tok::Star => AstNode::UnaryOp { 
                op: UnaryOp::Deref, 
                expr: Box::new(self.parse_expr(Self::PREFIX_BP).node) 
            },

            Tok::LPar => {
                let expr = self.parse_expr(0);
                self.expect(Tok::RPar);
                if let Some(t) = self.peek() {
                    if t.tok == Tok::DollarSign {
                        self.consume();
                        
                        let tgt_ftype = self.parse_ftype();

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
                buf.push(AstNode::Variable(idt.clone()));

                while let Some(nexttok) = self.peek() {
                    match &nexttok.tok.clone() {
                        Tok::Semicol => {
                            break;
                        }
                        Tok::Equals => {
                            self.consume();
                            let nameval = Box::new(buf.last().cloned()
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

                                    let name_node = buf.last()
                                        .expect(&format!("{}: expected name before \
                                            compound assign", self.line));

                                    let new_val_node = AstNode::BinaryOp { 
                                        op: bop, 
                                        left: Box::new(name_node.clone()), 
                                        right: Box::new(right.node) 
                                    };

                                    return AstNode::Reassignment { 
                                        name: Box::new(name_node.clone()),
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
                            let ftype = self.parse_ftype();

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
                            let astn = buf.last().expect(&format!(
                                    "{}: Expected value of fieldaddr",
                                    self.line,
                                )).clone();
                            let astr = AstRoot::new(astn, self.line);
                            if self.peek_is(Tok::LPar) {
                                let mut args = self.parse_args_call();
                                args.insert(0, astr);
                                let func_name = AstNode::string_to_path(&field_name);

                                buf.push(AstNode::MethodCall { 
                                    name: Box::new(func_name), 
                                    args, 
                                    idx: self.call_ctr 
                                });
                                self.call_ctr += 1;
                            } else {
                                buf.push(AstNode::StructFieldAddr { 
                                    val: Box::new(astr), 
                                    field_name 
                                });
                            }
                        }
                        _other => {break;}
                    }
                }

                match buf.last() {
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
                        ftype = match self.parse_ftype() {
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
                match intr {
                    Intrinsic::Sizeof => {
                        if self.peek_is(Tok::At) {
                            self.consume();
                            let ft = self.parse_ftype();
                            let s = ft.to_string().replace("s_", "");
                            return AstNode::Intrinsic { 
                                intr: *intr, 
                                val: Box::new(AstNode::Variable(s))
                            };
                        }
                    }
                    _other => {}
                }
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

                let is_public = self.prev_flags.contains(&ParseFlags::Public); 
                
                AstNode::FunctionOverload { 
                    func: Box::new(f.0),
                    idx: idx,
                    public: is_public
                }
            }

            Tok::Keyword(Kword::Return) => {
                if let Some(t) = self.peek() {
                    if t.tok == Tok::Semicol {
                        return AstNode::ReturnVal { val: Box::new(AstRoot::new( 
                                AstNode::none, self.line
                            ))
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

            Tok::Keyword(Kword::Impl) => {
                let res = self.parse_impl();
                res
            }

            Tok::Keyword(Kword::Trait) => {
                let res = self.parse_trait();
                let ti = TraitInfo::from_astn(&res);
                self.traits.t.insert(ti.path.path_to_string(), ti);
                res
            }

            Tok::Keyword(Kword::Usemod) => {
                let first = match self.expect_idt() {
                    Some(v) => v,
                    None => {
                        let found = self.peek().map_or(Tok::EOF, |t| t.tok.clone());
                        return AstNode::Invalid(
                            LogLevel::Error(ErrKind::ParseExpectedIdt(found))
                        );
                    }
                };
                let path = self.parse_path(first);
                AstNode::Usemod { 
                    name: Box::new(path)
                }
            }

            Tok::Hash => {
                self.expect(Tok::LBr);
                let mut arr: Vec<Attr> = Vec::new();
                let line = self.line;
                while let Some(t) = self.consume() {
                    let t = t.clone();
                    match &t.tok {
                        Tok::Identifier(idt) => {
                            let args: Vec<String> = if self.peek_is(Tok::LPar) {
                                self.consume();
                                let mut res = Vec::new();
                                while let Some(ta) = self.consume() {
                                    match &ta.tok {
                                        Tok::Identifier(idt) => {
                                            res.push(idt.to_owned());       
                                        }
                                        Tok::Comma => {}
                                        Tok::RPar => {break;}
                                        other => unimplemented!("{}: attribute {:#?}", 
                                            line, other)
                                    }
                                }
                                res
                            } else {
                                Vec::new()
                            };
                            let attr: Attr = Attr::from_str(&idt, &args);
                            arr.push(attr);
                        }
                        Tok::Comma => {},
                        Tok::RBr => {
                            break;
                        }
                        other => panic!("{}: unexpected tok {:?} in attribute parse",
                            line, other)
                    }
                };
                self.prev_flags.insert(ParseFlags::Attrs(arr));
                AstNode::none
            }
    
            other => {
                if Some(other) == self.allowed_tok.as_ref() {
                    return self.parse_expr(255).node;
                }
                panic!("{}: FCparse unexpected token `{:?}`", line_n, other);
            }
        }
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
        let mut generics = HashSet::new();

        while let Some(tok) = self.peek() {
            match &tok.tok {
                Tok::Combined(t1, t2)
                    if matches!((t1.as_ref(), t2.as_ref()), (Tok::Colon, Tok::Colon)) =>
                {
                    self.consume(); 
                    let next = self.expect_idt()
                        .expect("Expected identifier after ::");
                    segments.push(next);
                },
                Tok::LAngBr => {
                    self.consume();
                    loop {
                        if self.peek_is(Tok::RAngBr) {
                            self.consume();
                            break;
                        } else if self.peek_is(Tok::Comma) {
                            self.consume();
                        }

                        let name = unwrap_or_invalid!(self.expect_idt(), self); 
                        let mut bounds = Vec::new();
                        if self.peek_is(Tok::Colon) {
                            self.consume();
                            self.expect(Tok::LBr);
                            while let Some(tokb) = self.peek() {
                                match &tokb.tok {
                                    Tok::Identifier(idt) => {
                                        let path = self.parse_path(idt.clone());
                                        bounds.push(path.path_to_string());
                                        self.consume();
                                    }
                                    Tok::RBr => {
                                        self.consume();
                                        break;
                                    }
                                    other => {
                                        return AstNode::Invalid(LogLevel::Error(
                                            ErrKind::ParseUnexpected(other.clone())
                                            )
                                        );
                                    } 
                                }
                            }
                        }
                        let g = GenericType::new(name, bounds);
                        generics.insert(g);
                    }
                }  
                _ => break,
            }
        }

        AstNode::Path { 
            segments,
            generic: generics,
        }
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

    

    pub fn match_bop_for_tok(&mut self, tok: &Tok, _next_tok: Option<&Tok>) -> Option<BinaryOp> {
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

        let is_public = self.prev_flags.contains(&ParseFlags::Public);

        if !externed {
            let mut body = self.parse_expr(0);
            if !body.attrs.is_empty() {
                self.prev_flags.insert(ParseFlags::Attrs(
                    body.attrs.drain(..).collect()
                ));
            }

            (AstNode::Function { 
                name: Box::new(name.clone()), 
                args: args, 
                ret_type: ret_type, 
                body: Box::new(body.node),
                public: is_public 
            }, name.path_to_string())
        } else {
            (AstNode::ExternedFunc { 
                name: Box::new(name.clone()),
                args: args, 
                ret_type: ret_type,
                public: is_public,
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
                    let ft = FType::Array(el_ft.to_idx(), 0, 0);

                    res.push(FuncArg::new(arg_name, ft));
                    self.expect(Tok::RBr);
                    continue;
                }
            };

            let ft = self.parse_ftype(); 

            res.push(FuncArg::new(arg_name, ft));
        };

        res
    }

    fn parse_ftype(&mut self) -> FType {
        let mut is_ptr = false;
        let mut is_arr = false;
        if self.peek_is(Tok::Star) {
            self.consume();
            is_ptr = true;
        } else if self.peek_is(Tok::LBr) {
            self.consume();
            is_arr = true;
        }

        let arg_typename_start = self.expect_idt().unwrap_or_else(|| {
            panic!("{}: expected typename for arg", self.line)}
        );

        let is_h = arg_typename_start.starts_with("h_");
        let is_s = arg_typename_start.starts_with("s_");
        let arg_typename = match (is_s, is_ptr, is_h) {
            (true, false, false) => {
                let path_start = arg_typename_start;
                let path = self.parse_path(path_start);
                format!("{}", path
                    .prep_module_at(&self.curmod, 2)
                    .path_to_string())
            } 
            (false, true, false) => {
                let path = self.parse_path(arg_typename_start);
                format!("ptr_{}", path
                    .prep_module_at(&self.curmod, 0)
                    .path_to_string())
            }
            (false, false, true) => {
                let path_start = arg_typename_start;
                let path = self.parse_path(path_start);
                format!("{}", path
                    .prep_module_at(&self.curmod, 2)
                    .path_to_string())

            }
            (false, false, false) => {
                arg_typename_start
            }
            _other => {
                unreachable!()
            }
        };

        let ft = match_ftype(&arg_typename, &mut self.nm_interner)
            .unwrap_or_else(|| {
            panic!("{}: unknown type {}", self.line, arg_typename)}
        );

        if is_arr {
            self.expect(Tok::RBr);
            FType::Array(ft.to_idx(), 0, 0)
        } else {
            ft
        }
    }

    fn parse_func_rettype(&mut self) -> FType {
        if let Some(t) = self.peek() {
            if t.tok != Tok::Combined(Box::new(Tok::Minus), Box::new(Tok::RAngBr)) {
                return FType::none;
            }

            self.consume();
            self.parse_ftype()
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

        let attrs: Vec<Attr> = self.prev_flags.iter().map(|f| {
            match &f {
                ParseFlags::Attrs(attrs) => attrs.clone(),
                other => Vec::new()
            }
        }).flatten().collect();

        AstNode::Structure { 
            name: Box::new(name), 
            fields: fields,
            public: self.prev_flags.contains(&ParseFlags::Public),
            attrs: attrs,
        }
    }

    fn parse_struct_fields(&mut self) -> Vec<AstNode> {
        let mut res: Vec<AstNode> = Vec::new();

        self.expect(Tok::LCurBr);
        loop {
            let mut is_public = false;
            if self.peek_is(Tok::Keyword(Kword::Pub)) {
                self.consume();
                is_public = true;
            }

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
                    let ft = self.parse_ftype();
                    res.push(AstNode::StructField { 
                        name: idt.clone(), 
                        ftype: ft,
                        public: is_public,
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

    fn parse_impl(&mut self) -> AstNode {
        let name = self.path_helper();
        let mut trait_impl = false;

        let name_struct = if self.peek_is(Tok::Keyword(Kword::For)) {
            self.consume();
            let name_struct = self.path_helper();
            trait_impl = true;

            let nm_stc_s = name_struct.path_to_string();
            match self.trait_impls.get_mut(&nm_stc_s) {
                Some(v) => {v.insert(name.path_to_string());},
                None => {
                    self.trait_impls.insert(nm_stc_s, HashSet::from(
                            [name.path_to_string()]
                        ));
                }
            }
            
            self.prev_flags.insert(ParseFlags::TraitImpl(name.path_to_string()));
            name_struct
        } else {
            name.clone()
        };
        let st_name = name_struct.path_to_string();

        self.prev_flags.insert(ParseFlags::StructImpl(st_name.clone()));

        let old_mod = self.curmod.clone();
        self.curmod = st_name.clone();
        let body = self.parse_expr(0);
        self.curmod = old_mod;
        
        self.prev_flags.remove(&ParseFlags::StructImpl(st_name.clone()));

        if !trait_impl {
            AstNode::StructImpl {
                name: Box::new(name),
                body: Box::new(body),
                Trait: None,
            }
        } else {
            self.prev_flags.remove(&ParseFlags::TraitImpl(st_name));
            AstNode::StructImpl {
                name: Box::new(name_struct),
                body: Box::new(body),
                Trait: Some(Box::new(name)),
            }
        }
    }

    fn path_helper(&mut self) -> AstNode {
        let name_start = self.expect_idt().unwrap_or_else(|| {
            panic!("{}: Expected function name", self.line)
        });

        let name_raw = self.parse_path(name_start);
        let name_raw_st = name_raw.path_to_string();
        let name = match name_raw_st.contains("::") {
            true => {
                name_raw 
            }
            false => {
                let withmod = format!("{}::{}", self.curmod, name_raw_st);
                let mut wmod = AstNode::string_to_path(&withmod);
                wmod.add_generics(name_raw.get_generics());
                wmod
            }
        };
        name
    }

    fn parse_trait(&mut self) -> AstNode {
        let public = self.prev_flags.contains(&ParseFlags::Public);

        let name = self.path_helper();
        let generic_names = name.get_generic_names();
        
        self.prev_flags.insert(ParseFlags::Trait(generic_names.clone()));

        let body = self.parse_expr(0);

        self.prev_flags.remove(&ParseFlags::Trait(generic_names));

        AstNode::Trait {
            name: Box::new(name),
            body: Box::new(body.node),
            public,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AstNode {
    none,
    NoParse, // internal astnode to stop parsing expr
    Invalid(LogLevel), // invalid node

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
        segments: Vec<String>,
        generic:  HashSet<GenericType>,
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
        public: bool,
        attrs: Vec<Attr>,
    },

    StructField {
        name: String,
        ftype: FType,
        public: bool,
    },

    StructCreate {
        name: Box<AstNode>, // astnode::path 
        field_vals: HashMap<String, Box<AstNode>>,
    },

    StructFieldAddr {
        val: Box<AstRoot>,
        field_name: String,
    },


    StructImpl {
        name: Box<AstNode>,
        body: Box<AstRoot>,
        Trait: Option<Box<AstNode>>,
    },

    MethodCall {
        name: Box<AstNode>,
        args: Vec<AstRoot>,
        idx: usize,
    },

    Usemod {
        name: Box<AstNode>, // path
    },

    Trait {
        name: Box<AstNode>,
        body: Box<AstNode>,
        public: bool,
    },
}

impl AstNode {
    /// Get path segments, 
    /// panic if its not a path node.
    pub fn path_to_segs(&self) -> Vec<String> {
        // TODO: generics here 
        match self {
            AstNode::Path { segments, .. } => {
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
        AstNode::Path { 
            segments: segs.clone(), 
            generic: HashSet::new() 
        }
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

        let (unprefixed, pref) = remove_struct_pref(&st);
        if module.ends_with(&unprefixed) {
            st = format!("{}{}", pref, module.to_owned());
        } else {
            match st.contains("::") {
                true => {},
                false => {
                    st.insert_str(idx, 
                        &format!("{}::", module)
                    ); 
                }
            }
        }
        Self::string_to_path(&st)
    }

    pub fn get_generic_names(&self) -> Vec<String> {
        match self {
            AstNode::Path { segments, generic } => {
                let mut res = Vec::new();
                for g in generic {
                    res.push(g.name.clone());
                }
                res
            }
            other => unreachable!("Expected path node, found {:#?}", other)
        } 
    }

    pub fn get_generics(&self) -> HashSet<GenericType> {
        match self {
            AstNode::Path { segments, generic } => {
                generic.clone()
            }
            other => unreachable!("Expected path node, found {:#?}", other)
        } 
    }

    pub fn add_generics(&mut self, gs: HashSet<GenericType>) {
        match self {
            AstNode::Path { generic, .. } => {
                generic.extend(gs);
            }
            other => unreachable!("Expected path node, found {:#?}", other),
        }
    }

    pub fn can_have_attrs(&self) -> bool {
        match self {
            AstNode::CodeBlock { exprs } => true,
            AstNode::Structure { name, fields, public, attrs } => true,
            AstNode::StructImpl { name, body, Trait } => true,
            AstNode::Function { name, args, ret_type, body, public } => true,
            AstNode::FunctionOverload { func, idx, public } => true,
            AstNode::ExternedFunc { name, real_name, args, ret_type, public } => true,
            AstNode::Module { name, node } => true,
            other => false,
        }
    }
}

pub fn remove_struct_pref(s: &str) -> (String, String) {
    let prefixes = ["h_", "s_", "ptr_"];
    
    for prefix in prefixes {
        if s.starts_with(prefix) {
            return (s[prefix.len()..].to_string(), prefix.to_owned());
        }
    }
    
    (s.to_string(), String::new())
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
    AddressOf,
    Deref,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParseFlags {
    Public,
    StructImpl(String),
    Attrs(Vec<Attr>),
    Trait(Vec<String>), // generic typenames
    TraitImpl(String),
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
//    generic_names: HashSet<String>) -> Option<FType> {
    match lit {
        // any if generic_names.contains(any) => {
        //     // TODO
        //     Some(FType::Generic(0))
        // }
        "uint" => Some(FType::uint),
        "int" => Some(FType::int),
        "double" => Some(FType::double),
        "bool" => Some(FType::bool),
        "str" => Some(FType::strconst),
        "single" => Some(FType::single),
        "float" => Some(FType::single),
        "u32" => Some(FType::u32),
        "i32" => Some(FType::i32),
        "ubyte" => Some(FType::ubyte),
        "ibyte" => Some(FType::ibyte),
        "ptr" => Some(FType::Ptr),
        other if lit.starts_with("s_") => Some(
            FType::Struct(interner.intern(&lit[2..]))
        ),
        other if lit.starts_with("ptr_") => {
            let slice = &lit[4..];
            Some(
                FType::StructPtr(interner.intern(slice))
            )
        }
        other if lit.starts_with("h_") => {
            let slice = &lit[2..];
            Some(
                FType::StructHeapPtr(interner.intern(slice))
            )
        }
        _other => None,
    }
}


#[derive(Debug, Clone)]
pub struct AstRoot {
    pub node: AstNode,
    pub line: usize,
    pub attrs: Vec<Attr>,
}

impl AstRoot {
    pub fn new(node: AstNode, line: usize) -> AstRoot {
        AstRoot { 
            node: node, 
            line: line,
            attrs: Vec::new(),
        }
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
            AstNode::Function { name, args, ret_type, body: _, public } => {
                let mut fdat = FuncDat::new(
                    *name.clone(), args.clone(), *ret_type, false
                );
                fdat.public = *public;
                Some(fdat)
            }
            AstNode::FunctionOverload { func, idx: _, public } => {
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

    pub fn from_several(mut fts: Vec<FuncTable>) -> FuncTable {
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

    /// Args: func name + used modules 
    pub fn get_func(&mut self, name: &str, usemods: &Vec<String>) 
        -> Option<&Vec<FuncDat>> {
        if let Some(v) = self.ft.get(name) {
            return Some(v);
        };

        for modnm in usemods {
            if let Some(v) = self.ft.get(&format!("{}::{}", modnm, name)) {
                return Some(v);
            };
        }

        return None;
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Attr {
    Heap,
    Target(Vec<Target>),
    Custom(String),
}

impl Attr {
    fn from_str(value: &str, args: &Vec<String>) -> Self {
        match value {
            "heap" => Attr::Heap,
            "target" => {
                let mut targets = Vec::new();
                for arg in args {
                    let tgt = match Target::from_str(arg, false) {
                        Ok(v) => v,
                        Err(e) => panic!("Target {} parsing exception: {}",
                            arg, e)
                    };
                    targets.push(tgt);
                }
                Attr::Target(targets)
            },
            other  => Attr::Custom(other.to_owned()), 
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericType {
    name:   String,
    bounds: Vec<String>, // vec of needed trait names
}

impl GenericType {
    pub fn new(name: String, bounds: Vec<String>) -> GenericType {
        GenericType { name, bounds }
    }
}

#[derive(Debug, Clone)]
pub struct TraitInfo {
    pub path: AstNode,
    pub req_funcs: HashMap<String, FuncDat>,
}

impl TraitInfo {
    pub fn from_astn(n: &AstNode) -> TraitInfo {
        match n {
            AstNode::Trait { name, body, public } => {
                let mut funcs = HashMap::new();
                match &**body {
                    AstNode::CodeBlock { exprs } => {
                        for e in exprs {
                            let err_msg = format!("Expected function, found {:#?}",
                                e.node);
                            let fdat = FuncDat::new_from_astn(&e.node)
                                .expect(&err_msg);
                            let segs = fdat.name.path_to_segs();
                            let fname = segs
                                .last()
                                .expect("Empty func name!");
                            funcs.insert(fname.to_owned(), fdat);
                        }
                    }
                    other => unreachable!("Expected codeblock, found {:#?}", other)
                }

                TraitInfo { 
                    path: *name.clone(), 
                    req_funcs: funcs
                }
            }
            other => unreachable!("Expected trait node, found {:#?}", other)
        }
    }
}

#[derive(Debug, Clone)]
pub struct TraitTable {
    pub t: HashMap<String, TraitInfo>,
}

impl TraitTable {
    pub fn new() -> TraitTable {
        TraitTable { 
            t: HashMap::new()
        }
    }

    pub fn from_several(mut tts: Vec<TraitTable>) -> TraitTable {
        let mut res = TraitTable::new();

        for tt in tts.drain(..) {
            res.t.extend(tt.t);
        }

        res
    }
}
