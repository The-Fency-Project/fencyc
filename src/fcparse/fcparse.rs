use std::{fs::File, io::{self, BufRead, BufReader}};

use crate::{lexer::lexer::{Kword, Tok, Token}, seman::seman::FType};

pub struct FcParser {
    tokens: Vec<Token>,
    pos: usize,
}


impl FcParser {
    pub fn new(toks: Vec<Token>) -> FcParser {
        FcParser { tokens: toks, pos: 0 }
    }

    pub fn parse_everything(&mut self) -> Vec<AstNode> {
        let mut res: Vec<AstNode> = Vec::new();
        while self.peek().is_some() {
            let expr = self.parse_expr(0);
            res.push(expr);
        }
        res
    }

    pub fn parse_expr(&mut self, min_bp: u8) -> AstNode {
        let mut left = self.parse_prefix();

        while let Some(tok) = self.peek() {
            let optok = &tok.tok.clone();

            if *optok == Tok::Semicol {
                self.pos += 1;
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

            left = AstNode::BinaryOp {
                op: match_bop_for_tok(optok).unwrap(),
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        left
    }

    fn parse_prefix(&mut self) -> AstNode {
        let token: &Token = self.consume().expect("unexpected EOF");
        let line_n: usize = token.line;

        match &token.tok {
            Tok::Int(iv) => AstNode::Int(*iv),

            Tok::Minus => AstNode::UnaryOp {
                op: UnaryOp::Negate,
                expr: Box::new(self.parse_expr(255)),
            },

            Tok::LPar => {
                let expr = self.parse_expr(0);
                self.expect(Tok::RPar);
                expr
            },

            Tok::Plus => self.parse_expr(255),

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
                    val: Box::new(expr), 
                    ft: ftype 
                }
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
            Tok::Plus | Tok::Minus => Some((10, 11)),
            Tok::Star | Tok::Slash => Some((20, 21)),
            Tok::Keyword(Kword::Let) => Some((5, 6)),
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
}

#[derive(Debug, Clone)]
pub enum AstNode {
    Int(i64),
    Float(f64),
    Uint(u64),
    StringLiteral(String),
    Identifier(String),

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

    Assignment {
        name: String,
        val: Box<AstNode>,
        ft: FType, 
    },
}

#[derive(Debug, Clone)]
pub enum BinaryOp {
    Add, 
    Substract,
    Multiply,
    Divide,
}

pub fn match_bop_for_tok(tok: &Tok) -> Option<BinaryOp> {
    match tok {
        Tok::Plus => Some(BinaryOp::Add),
        Tok::Minus => Some(BinaryOp::Substract),
        Tok::Star => Some(BinaryOp::Multiply),
        Tok::Slash => Some(BinaryOp::Divide),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Negate, 
    Not,
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
