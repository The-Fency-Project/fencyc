use std::{fs::File, io::{self, BufRead, BufReader}};

use crate::lexer::lexer::{Tok, Token};

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
            _ => None,
        }
    }

    fn consume(&mut self) -> Option<&Token> {
        let tok = self.tokens.get(self.pos); // <-- FIX: возвращаем текущий
        self.pos += 1;                       // и только потом двигаем pos
        tok
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }
}

#[derive(Debug, Clone)]
pub enum AstNode {
    Int(i64),
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
