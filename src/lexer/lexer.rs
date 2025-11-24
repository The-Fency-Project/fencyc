use std::{fs, io};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Int(i64),
    Plus,
    Minus,
    Star,
    Slash,
    LPar, // (
    RPar, // )
    Semicol,
    Keyword(Kword),
    Identifier(String),
    Equals, // =
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    pub line: usize,
}

impl Token {
    pub fn new(t: Tok, l: usize) -> Token {
        Token { tok: t, line: l }
    }
}

pub fn tokenize(filepath: &str) -> Vec<Token> {
    let contents = fs::read_to_string(filepath).unwrap();
    let mut chars = contents.chars().peekable();
    let mut res: Vec<Token> = Vec::new();
    let mut line: usize = 1;

    while let Some(&ch) = chars.peek() {
        match ch {
            '0'..='9' => {
                let mut num_st = String::new();
                while let Some('0'..='9') = chars.peek() {
                    num_st.push(chars.next().unwrap());
                }; 
                let nval: i64 = num_st.parse().unwrap();
                res.push(Token::new(Tok::Int(nval), line));
            }
            '+' => {res.push(Token::new(Tok::Plus, line)); chars.next();},
            '-' => {res.push(Token::new(Tok::Minus, line)); chars.next();},
            '*' => {res.push(Token::new(Tok::Star, line)); chars.next();},
            '/' => {res.push(Token::new(Tok::Slash, line)); chars.next();},
            '(' => {res.push(Token::new(Tok::LPar, line)); chars.next();},
            ')' => {res.push(Token::new(Tok::RPar, line)); chars.next();},
            ';' => {res.push(Token::new(Tok::Semicol, line)); chars.next();},
            '=' => {res.push(Token::new(Tok::Equals, line)); chars.next();},
            ' ' | '\t' => {chars.next();},
            '\n' => {line += 1; chars.next();}
            'l' => {
                let mut assign = String::new();
                // TODO: handle assignments here
            }
            other => {
                panic!("Unknown token: {}", other);
            }
        }
    }

    
    res
}

#[derive(Debug, Clone, PartialEq)]
pub enum Kword {
    Let,
}
