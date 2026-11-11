use std::{collections::{HashMap, HashSet, hash_map::Keys}, io::BufRead};

use clap::ValueEnum;

use crate::{cli::Target, lexer::lexer::{Intrinsic, Kword, Tok, Token}, logger::logger::{ErrKind, LogLevel}, mir::mir::{FVal, FValue}, seman::seman::{FType, StructTable}};

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
    pub traits: TraitTable,
    pub generic_funcs: HashMap<String, AstRoot>,
    pub generic_impls: HashMap<String, AstRoot>,
    pub generic_structs: Vec<(String, Vec<FType>)>,
    generic_params: Vec<String>,
    match_header: bool,
}

#[cfg(test)]
mod generic_lookahead_tests {
    use super::*;

    fn looks_generic(tokens: Vec<Tok>) -> bool {
        FcParser::new(tokens.into_iter().map(|tok| Token::new(tok, 1)).collect())
            .looks_like_generic_path()
    }

    #[test]
    fn generic_arguments_before_a_literal_are_recognized() {
        assert!(looks_generic(vec![Tok::LAngBr, Tok::Identifier("int".into()),
            Tok::RAngBr, Tok::LCurBr]));
    }

    #[test]
    fn comparison_cannot_scan_across_a_statement_into_a_match_arrow() {
        assert!(!looks_generic(vec![Tok::LAngBr, Tok::Identifier("argc".into()),
            Tok::Semicol, Tok::Identifier("i".into()), Tok::Equals,
            Tok::RAngBr, Tok::LCurBr]));
    }

    #[test]
    fn comparison_cannot_scan_across_an_operator_into_a_match_arrow() {
        assert!(!looks_generic(vec![Tok::LAngBr, Tok::Identifier("argc".into()),
            Tok::Equals, Tok::RAngBr, Tok::LCurBr]));
    }
}

#[cfg(test)]
mod alias_tests {
    use super::*;
    #[test]
    fn parses_module_aliases() {
        let mut parser = FcParser::new(crate::lexer::lexer::tokenize_source("use vendor::graphics as gfx;"));
        let ast = parser.parse_everything().0;
        assert!(matches!(&ast[0].node, AstNode::Usemod { alias: Some(alias), .. } if alias == "gfx"));
    }
    #[test]
    fn rejects_overload_without_base_function() {
        let mut parser = FcParser::new(crate::lexer::lexer::tokenize_source("overload func missing(x: int) { return; }"));
        let ast = parser.parse_everything().0;
        assert!(matches!(&ast[0].node, AstNode::Invalid(LogLevel::Error(ErrKind::OverrideUndeclared(name))) if name == "main::missing"));
    }
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
            traits: TraitTable::new(),
            generic_funcs: HashMap::new(),
            generic_impls: HashMap::new(),
            generic_structs: Vec::new(),
            generic_params: Vec::new(),
            match_header: false,
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

            if *optok == Tok::LPar {
                left = AstNode::CallValue { callee: Box::new(left), args: self.parse_args_call() };
                continue;
            }

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

            if *optok == Tok::DoubleDot {
                let end = match self.peek() {
                    None | Some(Token { tok: Tok::RBr | Tok::Semicol | Tok::Comma | Tok::RPar | Tok::RCurBr, .. }) => None,
                    _ => Some(Box::new(self.parse_expr(4).node)),
                };
                left = AstNode::Range {
                    start: Some(Box::new(left)),
                    end,
                };
                continue;
            }

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
            Tok::Semicol => AstNode::none,

            Tok::Int(iv) => AstNode::Int(*iv),
            Tok::Uint(uv) => AstNode::Uint(*uv),
            Tok::Double(fv) => AstNode::Double(*fv),
            Tok::strlit(s) => AstNode::StringLiteral(s.to_owned()),
            Tok::I32(iwv) => AstNode::I32(*iwv),
            Tok::Single(sv) => AstNode::Single(*sv),
            Tok::U32(uwv) => AstNode::U32(*uwv),
            Tok::Ishort(ihv) => AstNode::Ishort(*ihv),
            Tok::Ushort(uhv) => AstNode::Ushort(*uhv),
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

            Tok::DoubleDot => {
                // An omitted lower bound (`..end`). The right hand side is
                // parsed at range precedence so arithmetic in the bound is
                // still part of the range expression.
                let end = match self.peek() {
                    None | Some(Token { tok: Tok::RBr | Tok::Semicol | Tok::Comma | Tok::RPar | Tok::RCurBr, .. }) => None,
                    _ => Some(Box::new(self.parse_expr(4).node)),
                };
                AstNode::Range { start: None, end }
            }

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
                let ft = self.parse_ftype();

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
                                    } else if self.peek_is(Tok::LCurBr) && !self.match_header {
                                        return self.parse_struct_create(&path);
                                    } else {
                                        return AstNode::Variable(path.path_to_string());
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

                            return AstNode::ExprCast {
                                expr: Box::new(buf.last().unwrap().clone()),
                                target_type: ftype,
                            }
                        }
                        Tok::LPar => { // function call
                            if !matches!(buf.last(), Some(AstNode::Variable(_))) {
                                let callee = Box::new(buf.last().unwrap().clone());
                                return AstNode::CallValue { callee, args: self.parse_args_call() };
                            }
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

                            let base = Box::new(buf.last().unwrap().clone());
                            let n = if matches!(&idx_ast.node, AstNode::Range { .. }) {
                                AstNode::ArraySlice(base, Box::new(idx_ast))
                            } else {
                                AstNode::ArrayElem(base, Box::new(idx_ast))
                            };
                            buf.push(n);
                        }
                        Tok::LAngBr if self.looks_like_generic_path() => {
                            let path = self.parse_path(idt_cl.clone());
                            if self.peek_is(Tok::LCurBr) {
                                let n = self.parse_struct_create(&path);
                                buf.push(n);
                            } else {
                                buf.push(AstNode::Variable(path.path_to_string()));
                            }
                        }
                        Tok::LCurBr if !self.match_header => {
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
                let fdat = FuncDat::new_from_astn(&f.0)
                    .expect(&format!("{}: Expected func", self.line));
                if !fdat.name.get_generics().is_empty() {
                    self.generic_funcs.insert(
                        fdat.name.path_to_string(),
                        AstRoot::new(f.0.clone(), self.line)
                    );
                }
                self.funcs.push_func(fdat);
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
                    let Some(h) = self.overload_ctr.get_mut(&f.1) else {
                        return AstNode::Invalid(LogLevel::Error(ErrKind::OverrideUndeclared(f.1)));
                    };
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

            Tok::Keyword(Kword::Union) => {
                let res = self.parse_union();
                self.structs.push_from_astn(&res);
                res
            }

            Tok::Keyword(Kword::Enum) => {
                let res = self.parse_enum();
                self.structs.push_from_astn(&res);
                res
            }

            Tok::Keyword(Kword::Match) => self.parse_match(),

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
                let alias = if self.peek_is(Tok::Keyword(Kword::As)) {
                    self.consume();
                    Some(self.expect_idt().unwrap_or_else(|| panic!("{}: expected alias", self.line)))
                } else { None };
                AstNode::Usemod { 
                    name: Box::new(path), alias
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
        if let Some(ft) = match_ftype(&path) {
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
        let mut generic_order = Vec::new();

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
                    // loop of catching generic params 
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
                                        let path = self.path_helper();
                                        bounds.push(path.path_to_string());
                                    }
                                    Tok::RBr => {
                                        self.consume();
                                        break;
                                    }
                                    Tok::Comma => {
                                        self.consume();
                                        continue;
                                    }
                                    other => {
                                        let ot_cl = other.clone();
                                        self.consume();
                                        return AstNode::Invalid(LogLevel::Error(
                                            ErrKind::ParseUnexpected(ot_cl)
                                            )
                                        );
                                    } 
                                }
                            }
                        }
                        let g = GenericType::new(name, bounds);
                        generic_order.push(g.name.clone());
                        generics.insert(g);
                    }
                }  
                _ => break,
            }
        }


        AstNode::Path { 
            segments,
            generic: generics,
            generic_order,
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
        let old_header = std::mem::replace(&mut self.match_header, false);

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

        self.match_header = old_header;
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
            Tok::DoubleDot => Some((4, 5)),

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

    fn looks_like_generic_path(&self) -> bool {
        let mut depth = 0usize;
        for idx in self.pos..self.tokens.len() {
            match &self.tokens[idx].tok {
                Tok::LAngBr => depth += 1,
                Tok::RAngBr if depth > 0 => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.tokens.get(idx + 1).map(|t| &t.tok),
                            Some(Tok::LCurBr) | Some(Tok::LPar));
                    }
                }
                // Only scan tokens that can belong to a generic argument list.
                // In particular, never cross statements or match arrows while
                // deciding whether an expression's `<` means comparison.
                Tok::Identifier(_) | Tok::Comma | Tok::Colon | Tok::LBr | Tok::RBr => {}
                Tok::Combined(left, right)
                    if matches!((left.as_ref(), right.as_ref()), (Tok::Colon, Tok::Colon)) => {}
                _ => return false,
            }
        }
        false
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn parse_if(&mut self) -> AstNode {
        let old_header = std::mem::replace(&mut self.match_header, true);
        let condition = self.parse_expr(0); 
        self.match_header = old_header;

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
        let old_header = std::mem::replace(&mut self.match_header, true);
        let condition = self.parse_expr(0);
        self.match_header = old_header;

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

        let mut active_generic_params = self.generic_params.clone();
        active_generic_params.extend(name.get_generic_names());
        active_generic_params.sort();
        active_generic_params.dedup();
        let old_generic_params = std::mem::replace(
            &mut self.generic_params,
            active_generic_params,
        );

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

            let result = AstNode::Function {
                name: Box::new(name.clone()), 
                args: args, 
                ret_type: ret_type, 
                body: Box::new(body.node),
                public: is_public 
            };
            self.generic_params = old_generic_params;
            (result, name.path_to_string())
        } else {
            let result = AstNode::ExternedFunc {
                name: Box::new(name.clone()),
                args: args, 
                ret_type: ret_type,
                public: is_public,
                real_name: Box::new(AstNode::string_to_path(&name_start)),
            };
            self.generic_params = old_generic_params;
            (result, name.path_to_string())
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

            if self.peek_is(Tok::Ellipsis) {
                self.consume();
                res.push(FuncArg::new("__c_varargs".into(), FType::Variadic(Box::new(FType::none))));
                continue;
            }

            let arg_name = self.expect_idt().unwrap_or_else(|| {
                panic!("{}: expected arg name", self.line)}
            );
            self.expect(Tok::Colon);
            if self.peek_is(Tok::Ellipsis) {
                self.consume();
                let ft = self.parse_ftype();
                res.push(FuncArg::new(arg_name, FType::Variadic(Box::new(ft))));
                continue;
            }
            if let Some(v) = self.peek() {
                if v.tok == Tok::LBr {
                    self.consume();
                    let arg_typename = self.expect_idt().unwrap_or_else(|| {
                        panic!("{}: expected typename for arg", self.line)}
                    );
                    let el_ft = match_ftype(&arg_typename)
                        .or_else(|| self.generic_params.iter()
                            .find(|g| *g == &arg_typename)
                            .map(|g| FType::Generic(g.clone())))
                        .unwrap_or_else(|| {
                        panic!("{}: unknown type {}", self.line, arg_typename)}
                    );
                    let ft = FType::Array(
                        Box::new(el_ft.clone()), 
                        0
                    );

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
        if self.peek_is(Tok::Keyword(Kword::Func)) {
            self.consume();
            self.expect(Tok::LPar);
            let mut args = Vec::new();
            while !self.peek_is(Tok::RPar) {
                if !args.is_empty() { self.expect(Tok::Comma); }
                if self.peek_is(Tok::Ellipsis) {
                    self.consume();
                    let tail = if self.peek_is(Tok::RPar) { FType::none } else { self.parse_ftype() };
                    args.push(FType::Variadic(Box::new(tail)));
                    break;
                }
                args.push(self.parse_ftype());
            }
            self.expect(Tok::RPar);
            return FType::Function(args, Box::new(self.parse_func_rettype()));
        }
        let mut is_ptr = false;
        let mut is_arr = false;
       
        if self.peek_is(Tok::LBr) {
            self.consume();
            is_arr = true;
        }
        if self.peek_is(Tok::Star) {
            self.consume();
            is_ptr = true;
        } 
        

        let arg_typename_start = self.expect_idt().unwrap_or_else(|| {
            panic!("{}: expected typename for arg", self.line)}
        );

        if arg_typename_start == "slice" && self.peek_is(Tok::LBr) {
            self.consume();
            let element = self.parse_ftype();
            self.expect(Tok::RBr);
            return FType::Slice(Box::new(element));
        }

        let is_h = arg_typename_start.starts_with("h_");
        let is_s = arg_typename_start.starts_with("s_");

        let is_generic_name = self.generic_params.iter()
            .any(|g| g == if is_s || is_h { &arg_typename_start[2..] } else { &arg_typename_start });

        let mut ft = if is_generic_name && (is_s || is_h || is_ptr) {
            if is_h {
                FType::StructHeapPtr(arg_typename_start[2..].to_owned())
            } else if is_ptr {
                FType::StructPtr(arg_typename_start.clone())
            } else {
                FType::Struct(arg_typename_start[2..].to_owned())
            }
        } else if is_s || is_h || is_ptr {
            let path = self.parse_path(arg_typename_start.clone())
                .prep_module_at(&self.curmod, if is_ptr { 0 } else { 2 });
            let base = strip_type_prefix(&path.path_to_string());
            let generic_names = path.get_generic_names();
            if !generic_names.is_empty() {
                let args: Vec<FType> = generic_names.iter()
                    .map(|arg| self.generic_arg_type(arg))
                    .collect();
                self.generic_structs.push((base.clone(), args.clone()));
                let concrete = generic_instance_name(&base, &args);
                if is_ptr {
                    FType::StructPtr(concrete)
                } else if is_h {
                    FType::StructHeapPtr(concrete)
                } else {
                    FType::Struct(concrete)
            }
            } else {
                let typed = if is_ptr {
                    format!("ptr_{}", base)
                } else if is_s {
                    format!("s_{}", base)
                } else {
                    format!("h_{}", base)
        };
                match_ftype(&typed).unwrap_or_else(|| {
                    panic!("{}: unknown type {}", self.line, typed)
                })
            }
        } else {
            match_ftype(&arg_typename_start)
                .or_else(|| self.generic_params.iter()
                    .find(|g| *g == &arg_typename_start)
                    .map(|g| FType::Generic(g.clone())))
                .or_else(|| {
                    let path = self.parse_path(arg_typename_start.clone());
                    let base = self.qualify_generic_struct(&path.path_to_string());
                    let params = path.get_generic_names();
                    if params.is_empty() { Some(FType::Struct(base)) } else {
                        let args = params.iter().map(|arg| self.generic_arg_type(arg)).collect::<Vec<_>>();
                        self.generic_structs.push((base.clone(), args.clone()));
                        Some(FType::Struct(generic_instance_name(&base, &args)))
                    }
                })
            .unwrap_or_else(|| {
                    panic!("{}: unknown type {}", self.line, arg_typename_start)
                })
        };

        if is_arr {
            if self.peek_is(Tok::Semicol) {
                self.consume();
                let ct = self.expect_uint();
                self.expect(Tok::RBr);
                FType::Array(
                    Box::new(ft),
                    ct.1 as usize
                )
            } else {
                self.expect(Tok::RBr);
                FType::Array(
                    Box::new(ft), 
                    0
                )
            }
        } else {
            ft
        }
    }

    fn generic_arg_type(&self, arg: &str) -> FType {
        if let Some(ft) = match_ftype(arg) {
            return match ft {
                FType::Struct(st) => FType::Struct(self.qualify_generic_struct(&st)),
                FType::StructPtr(st) => FType::StructPtr(self.qualify_generic_struct(&st)),
                FType::StructHeapPtr(st) => FType::StructHeapPtr(self.qualify_generic_struct(&st)),
                other => other,
            };
        }
        if self.generic_params.iter().any(|g| g == arg) {
            return FType::Generic(arg.to_owned());
        }
        FType::Struct(self.qualify_generic_struct(arg))
    }

    fn qualify_generic_struct(&self, name: &str) -> String {
        if name.contains("::") {
            name.to_owned()
        } else {
            format!("{}::{}", self.curmod, name)
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

        let old_generic_params = std::mem::replace(
            &mut self.generic_params,
            name.get_generic_names(),
        );

        let fields = self.parse_struct_fields();

        self.generic_params = old_generic_params;

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

    fn parse_union(&mut self) -> AstNode {
        let name_start = self.expect_idt().expect("Expected union name");
        let name = self.parse_path(format!("{}::{}", self.curmod, name_start));
        let mut fields = self.parse_struct_fields();
        let attrs = vec![Attr::Custom("union".into())];
        AstNode::Structure {
            name: Box::new(name),
            fields: fields.drain(..).collect(),
            public: self.prev_flags.contains(&ParseFlags::Public),
            attrs,
        }
    }

    fn parse_enum(&mut self) -> AstNode {
        let name_start = self.expect_idt().expect("Expected enum name");
        let name = self.parse_path(format!("{}::{}", self.curmod, name_start));
        self.expect(Tok::LCurBr);
        let mut fields = Vec::new();
        loop {
            if self.peek_is(Tok::RCurBr) {
                self.consume();
                break;
            }
            let variant = self.expect_idt().expect("Expected enum variant");
            let ftype = if self.peek_is(Tok::LPar) {
                self.consume();
                let ty = self.parse_ftype();
                self.expect(Tok::RPar);
                ty
            } else {
                FType::none
            };
            fields.push(AstNode::StructField { name: variant, ftype, public: true });
            if self.peek_is(Tok::Comma) || self.peek_is(Tok::Semicol) {
                self.consume();
            }
        }
        AstNode::Structure {
            name: Box::new(name),
            fields,
            public: self.prev_flags.contains(&ParseFlags::Public),
            attrs: vec![Attr::Custom("enum".into())],
        }
    }

    fn parse_match(&mut self) -> AstNode {
        self.match_header = true;
        let value = self.parse_expr(0);
        self.match_header = false;
        self.expect(Tok::LCurBr);
        let mut arms = Vec::new();
        while !self.peek_is(Tok::RCurBr) {
            let pattern = match self.consume().expect("Expected match pattern").tok.clone() {
                Tok::Int(v) => MatchPattern::Int(v),
                Tok::Uint(v) => MatchPattern::Uint(v),
                Tok::Keyword(Kword::True) => MatchPattern::Bool(true),
                Tok::Keyword(Kword::False) => MatchPattern::Bool(false),
                Tok::Identifier(name) if name == "_" => MatchPattern::Wildcard,
                Tok::Identifier(name) => {
                    let path = self.parse_path(name);
                    if self.peek_is(Tok::LPar) {
                        self.consume();
                        let binding = self.expect_idt().expect("Expected match payload binding");
                        self.expect(Tok::RPar);
                        MatchPattern::PathBinding(path, binding)
                    } else {
                        MatchPattern::Path(path)
                    }
                }
                other => panic!("Unsupported match pattern {:?}", other),
            };
            if self.peek_is(Tok::Combined(Box::new(Tok::Equals), Box::new(Tok::RAngBr))) {
                self.consume();
            } else {
                self.expect(Tok::Equals);
                self.expect(Tok::RAngBr);
            }
            let body = self.parse_expr(0);
            arms.push((pattern, body));
        }
        self.expect(Tok::RCurBr);
        AstNode::Match { value: Box::new(value), arms }
    }

    pub fn parse_struct_create(&mut self, path: &AstNode) -> AstNode {
        let mut st = path.path_to_string();
        let fin_path = match st.contains("::") {
            true => path.clone(),
            false => {
                st.insert_str(0, &format!("{}::", self.curmod));
                let mut p = AstNode::string_to_path(&st);
                p.add_generics(path.get_generics());
                if let AstNode::Path { generic_order, .. } = &mut p {
                    *generic_order = path.get_generic_names();
                }
                p
            }
        };

        let fin_path = if !fin_path.get_generics().is_empty() {
            let args = fin_path.get_generic_names().into_iter()
                .map(|arg| self.generic_arg_type(&arg))
                .collect::<Vec<_>>();
            let base = fin_path.path_to_string();
            self.generic_structs.push((base.clone(), args.clone()));
            AstNode::string_to_path(&generic_instance_name(&base, &args))
        } else {
            fin_path
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
            self.traits.add_impl(nm_stc_s.clone(), name.path_to_string()); 
            
            self.prev_flags.insert(ParseFlags::TraitImpl(name.path_to_string()));
            name_struct
        } else {
            name.clone()
        };
        let st_name = name_struct.path_to_string();

        self.prev_flags.insert(ParseFlags::StructImpl(st_name.clone()));

        let old_mod = self.curmod.clone();
        let old_generic_params = std::mem::replace(
            &mut self.generic_params,
            name_struct.get_generic_names(),
        );
        self.curmod = st_name.clone();
        let body = self.parse_expr(0);
        self.curmod = old_mod;
        self.generic_params = old_generic_params;
        
        self.prev_flags.remove(&ParseFlags::StructImpl(st_name.clone()));

        let result = if !trait_impl {
            AstNode::StructImpl {
                name: Box::new(name),
                body: Box::new(body),
                Trait: None,
            }
        } else {
                self.prev_flags.remove(&ParseFlags::TraitImpl(st_name.clone()));
            AstNode::StructImpl {
                name: Box::new(name_struct.clone()),
                body: Box::new(body),
                Trait: Some(Box::new(name)),
            }
        };
        if !name_struct.get_generics().is_empty() {
            self.generic_impls.insert(
                st_name,
                AstRoot::new(result.clone(), self.line),
            );
        }
        result
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
                if let AstNode::Path { generic_order, .. } = &mut wmod {
                    *generic_order = name_raw.get_generic_names();
                }
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
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
    Ishort(i16),
    Ushort(u16),
    Ibyte(i8),
    Ubyte(u8),
    boolVal(bool),
    StringLiteral(String),
    Variable(String),
    Array(FType, Vec<AstNode>),
    ArrayElem(Box<AstNode>, Box<AstRoot>), // arrname, idx val
    ArraySlice(Box<AstNode>, Box<AstRoot>), // arrname, range
    Range {
        start: Option<Box<AstNode>>,
        end: Option<Box<AstNode>>,
    },
    ArrRep(u64), // repeat array elems N times

    CodeBlock {
        exprs: Vec<AstRoot>,
    },

    Match {
        value: Box<AstRoot>,
        arms: Vec<(MatchPattern, AstRoot)>,
    },

    Path {
        segments: Vec<String>,
        generic:  HashSet<GenericType>,
        generic_order: Vec<String>,
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
    CallValue {
        callee: Box<AstNode>,
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
        alias: Option<String>,
    },

    Trait {
        name: Box<AstNode>,
        body: Box<AstNode>,
        public: bool,
    },
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub enum MatchPattern {
    Int(i64),
    Uint(u64),
    Bool(bool),
    Wildcard,
    Path(AstNode),
    PathBinding(AstNode, String),
}

impl AstNode {
    /// Get path segments, 
    /// panic if its not a path node.
    pub fn path_to_segs(&self) -> Vec<String> {
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
            generic: HashSet::new(),
            generic_order: Vec::new(),
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
        let mut result = Self::string_to_path(&st);
        result.add_generics(self.get_generics());
        if let AstNode::Path { generic_order, .. } = &mut result {
            *generic_order = self.get_generic_names();
        }
        result
    }

    pub fn get_generic_names(&self) -> Vec<String> {
        match self {
            AstNode::Path { generic_order, generic, .. } => {
                if !generic_order.is_empty() {
                    generic_order.clone()
                } else {
                    let mut res: Vec<String> = generic.iter()
                        .map(|g| g.name.clone())
                        .collect();
                    res.sort();
                res
            }
            }
            other => unreachable!("Expected path node, found {:#?}", other)
        } 
    }

    pub fn get_generics(&self) -> HashSet<GenericType> {
        match self {
            AstNode::Path { generic, .. } => {
                generic.clone()
            }
            other => unreachable!("Expected path node, found {:#?}", other)
        } 
    }

    pub fn add_generics(&mut self, gs: HashSet<GenericType>) {
        match self {
            AstNode::Path { generic, generic_order, .. } => {
                generic.extend(gs);
                for g in generic.iter() {
                    if !generic_order.contains(&g.name) {
                        generic_order.push(g.name.clone());
                    }
                }
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

    pub fn get_func_name(&self) -> String {
        match self {
            AstNode::Function { name, args, ret_type, body, public } => {
                name.path_to_string()
            }
            AstNode::FunctionOverload { func, idx, public } => {
                Self::get_func_name(&*func)
            }
            AstNode::ExternedFunc { name, real_name, args, ret_type, public } => {
                name.path_to_string()
            }
            other => panic!("Unexpected ast node {:?} in get func name", other)
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

pub fn strip_type_prefix(s: &str) -> String {
    remove_struct_pref(s).0
}

pub fn type_key(ft: &FType) -> String {
    match ft {
        FType::Struct(name) => format!("s_{}", name),
        FType::StructPtr(name) => format!("ptr_{}", name),
        FType::StructHeapPtr(name) => format!("h_{}", name),
        FType::Array(el, count) => format!("arr_{}_{}", type_key(el), count),
        FType::Slice(el) => format!("slice_{}", type_key(el)),
        FType::Generic(name) => name.clone(),
        other => format!("{}", other),
    }
}

pub fn generic_instance_name(base: &str, args: &[FType]) -> String {
    let mut result = base.to_owned();
    for arg in args {
        result.push_str("::");
        result.push_str(&type_key(arg));
    }
    result
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Copy)]
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Copy)]
pub enum UnaryOp {
    Negate, 
    Not,
    LogicalNot,
    AddressOf,
    Deref,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Copy)]
pub enum CmpOp {
    Eq, // ==
    Ge, // >=
    G, // >
    L, // <
    Le, // <=
    Ne, // !=
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParseFlags {
    Public,
    StructImpl(String),
    Attrs(Vec<Attr>),
    Trait(Vec<String>), // generic typenames
    TraitImpl(String),
}

pub fn match_ftype(lit: &str) -> Option<FType> {
    match lit {
        "uint" => Some(FType::uint),
        "int" => Some(FType::int),
        "double" => Some(FType::double),
        "bool" => Some(FType::bool),
        "str" => Some(FType::strconst),
        "single" => Some(FType::single),
        "float" => Some(FType::single),
        "u32" => Some(FType::u32),
        "i32" => Some(FType::i32),
        "ushort" => Some(FType::ushort),
        "ishort" => Some(FType::ishort),
        "ubyte" => Some(FType::ubyte),
        "ibyte" => Some(FType::ibyte),
        "ptr" => Some(FType::Ptr),
        "range" => Some(FType::Range),
        // A bare `slice` is only useful as a marker in diagnostics; concrete
        // slices are inferred from `array[range]` expressions.
        "slice" => Some(FType::Slice(Box::new(FType::any))),
        other if lit.starts_with("s_") => Some(
            FType::Struct(lit[2..].to_owned())
        ),
        other if lit.starts_with("ptr_") => Some(
            FType::StructPtr(lit[4..].to_owned())
        ),
        other if lit.starts_with("h_") => Some(
            FType::StructHeapPtr(lit[2..].to_owned())
        ),
        _other => None,
    }
}


#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
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

    pub fn into_fmir(&self) -> (FValue, FType) {
        (
            FValue::new(FVal::VarTmp(self.name.clone()), self.ftype.clone()),
            self.ftype.clone()
        )
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct FuncDat {
    pub name: AstNode,
    pub args: Vec<FuncArg>,
    pub ret_type: FType,
    pub externed: bool,
    pub public: bool,
    pub real_name: Option<String>,
}

impl FuncDat {
    pub fn function_type(&self) -> FType {
        FType::Function(self.args.iter().map(|a| a.ftype.clone()).collect(), Box::new(self.ret_type.clone()))
    }

    pub fn symbol_name(&self, overload: usize) -> String {
        self.real_name.clone().unwrap_or_else(|| format!("{}_{}", self.name.path_to_string().replace("::", "_"), overload))
    }

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
                    *name.clone(), args.clone(), ret_type.clone(), false
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
                    *name.clone(), args.clone(), ret_type.clone(), true
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct FuncTable {
    // function name
    pub ft: HashMap<String, Vec<FuncDat>>
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
    pub fn get_func(&self, name: &str, usemods: &Vec<String>) 
        -> Option<&Vec<FuncDat>> {
        if let Some(v) = self.ft.get(name) {
            return Some(v);
        };

        for modnm in usemods {
            let (alias, module) = modnm.split_once('=').unwrap_or(("", modnm.as_str()));
            let prefix = if alias == name.split("::").next().unwrap_or("") && !alias.is_empty() {
                name.replacen(alias, module, 1)
            } else { format!("{}::{}", module, name) };
            if let Some(v) = self.ft.get(&prefix) {
                return Some(v);
            };
        }

        return None;
    }

}


#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericType {
    pub name:   String,
    pub bounds: Vec<String>, // vec of needed trait names
}

impl GenericType {
    pub fn new(name: String, bounds: Vec<String>) -> GenericType {
        GenericType { name, bounds }
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct TraitTable {
    pub t: HashMap<String, TraitInfo>,
    pub impls: HashMap<String, HashSet<String>>, // struct -> traits
}

impl TraitTable {
    pub fn new() -> TraitTable {
        TraitTable { 
            t: HashMap::new(),
            impls: HashMap::new(),
        }
    }

    pub fn from_several(mut tts: Vec<TraitTable>) -> TraitTable {
        let mut res = TraitTable::new();

        for tt in tts.drain(..) {
            res.t.extend(tt.t);
            res.impls.extend(tt.impls);
        }

        res
    }

    pub fn add_impl(&mut self, sname: String, tname: String) {
        if let Some(s) = self.impls.get_mut(&sname) {
            s.insert(tname);
        } else {
            let mut hs = HashSet::new();
            hs.insert(tname);
            self.impls.insert(sname, hs);
        }
    }
}
