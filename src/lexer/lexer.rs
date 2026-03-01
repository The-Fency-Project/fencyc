use std::{char, fs, io, iter::Peekable};

use crate::seman::seman::FType;

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Int(i64),
    Double(f64),
    Uint(u64),
    I32(i32),
    Single(f32),
    U32(u32),
    Ubyte(u8),
    Ibyte(i8), 
    strlit(String),
    Plus,
    Minus,
    Star,
    Slash,
    LPar, // (
    RPar, // )
    Colon, // :
    Semicol,
    Keyword(Kword),
    Identifier(String),
    Equals, // =
    RCurBr, //} 
    LCurBr, //{
    Ampersand, 
    Caret, // ^
    VerBar, // |
    DollarSign,
    Tilde,
    Exclam, // !
    Intrin(Intrinsic),
    LAngBr, // <
    RAngBr, // >
    DLAngBr, // <<
    DRAngBr, // >> 
    DoubleEq,
    RABEq, // >= (right ang brace and eq)
    ExclEq, // != 
    LABEq, // <=
    DoubleDot, // ..
    Dot,
    Comma,
    Percent, // %
    LBr,
    RBr,
    At, // @
    DQuote, // "
    Combined(Box<Tok>, Box<Tok>),
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
                let mut ftyp = FType::int;
                while let Some('0'..='9' | '.' | 'u' | 'i' | 'f' | 'w' | 'b') 
                    = chars.peek() {
                    let chn = chars.next().unwrap();
                    let peek = chars.peek();

                    match (chn, peek.copied()) {
                        ('.', any) => {
                            ftyp = FType::double;
                            num_st.push('.');
                        }
                        ('f', any) => { // f is expected to be in end
                            ftyp = FType::single;
                        }
                        ('u', Some('w')) => {
                            ftyp = FType::u32;
                        }
                        ('u', Some('b')) => {
                            ftyp = FType::ubyte;
                        }       
                        ('u', any) => {
                            ftyp = FType::uint;
                        }
                        ('i', Some('b')) => {
                            ftyp = FType::ibyte;
                        }
                        ('i', any) => {
                            ftyp = FType::i32;
                        }
                        other => { // int64, no suffix
                            num_st.push(chn);
                            continue;
                        }
                    }
                };

                match ftyp {
                    FType::int => {
                        let nval: i64 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::Int(nval), line));
                    }
                    FType::uint => {
                        let nval: u64 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::Uint(nval), line));
                    }
                    FType::double => {
                        let nval: f64 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::Double(nval), line));
                    }
                    FType::single => {
                        let nval: f32 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::Single(nval), line));
                    }
                    FType::i32 => {
                        let nval: i32 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::I32(nval), line));
                    }
                    FType::u32 => {
                        let nval: u32 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::U32(nval), line));
                    }
                    FType::ibyte => {
                        let nval: i8 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::Ibyte(nval), line));
                    }
                    FType::ubyte => {
                        let nval: u8 = num_st.parse().unwrap();
                        res.push(Token::new(Tok::Ubyte(nval), line));
                    }
                    other => unreachable!("Unexpected lexing error at line {}:\
                        got ftype {:?}", line, other)
                }
            }
            '+' | '-' | '*' | '^' | '&' | '|' | ':' => {
                chars.next();
                let combined = try_combine(&ch, chars.peek().copied(), line);
                if let Some(comb) = combined {
                    res.push(comb);
                    chars.next();
                } else {
                    let tok = match ch {
                        '+' => Tok::Plus,
                        '-' => Tok::Minus,
                        '*' => Tok::Star,
                        '^' => Tok::Caret,
                        '&' => Tok::Ampersand,
                        '|' => Tok::VerBar,
                        ':' => Tok::Colon,
                        other => panic!("{}: internal tok match error", line)
                    };
                    res.push(Token::new(tok, line));
                }
            },
            '/' => {
                chars.next();
                if let Some('/') = chars.peek() {
                    // ignoring comment
                    while chars.peek() != Some(&'\n') {
                        chars.next();
                    }
                } else {
                    let combine = try_combine(&ch, chars.peek().copied(), line);
                    if let Some(comb) = combine {
                        res.push(comb);
                        chars.next();
                    } else {
                        res.push(Token::new(Tok::Slash, line)); 
                    }
                }
            },
            '"' => {
                chars.next();
                let mut res_str = String::new();
                while let Some(ch) = chars.peek() {
                    if *ch == '"' {break;}
                    res_str.push(*ch);
                    chars.next();
                };
                res.push(Token::new(Tok::strlit(res_str), line));
                chars.next();
            }
            '[' => {res.push(Token::new(Tok::LBr, line)); chars.next();},
            ']' => {res.push(Token::new(Tok::RBr, line)); chars.next();},
            ',' => {res.push(Token::new(Tok::Comma, line)); chars.next();},
            '(' => {res.push(Token::new(Tok::LPar, line)); chars.next();},
            ')' => {res.push(Token::new(Tok::RPar, line)); chars.next();},
            ';' => {res.push(Token::new(Tok::Semicol, line)); chars.next();},
            '=' => {
                chars.next();
                if let Some('=') = chars.peek() {
                    res.push(Token::new(Tok::DoubleEq, line));
                    chars.next();
                } else {
                    res.push(Token::new(Tok::Equals, line)); 
                }
            },
            '%' => {res.push(Token::new(Tok::Percent, line)); chars.next();},
            ':' => {res.push(Token::new(Tok::Colon, line)); chars.next();},
            '}' => {res.push(Token::new(Tok::RCurBr, line)); chars.next();},
            '{' => {res.push(Token::new(Tok::LCurBr, line)); chars.next();},
            '$' => {res.push(Token::new(Tok::DollarSign, line)); chars.next();},
            '~' => {res.push(Token::new(Tok::Tilde, line)); chars.next();},
            '@' => {res.push(Token::new(Tok::At, line)); chars.next();},
            '!' => {
                chars.next();
                if Some('=') == chars.peek().copied() {
                    res.push(Token::new(Tok::ExclEq, line));
                    chars.next();
                } else {
                    res.push(Token::new(Tok::Exclam, line)); 
                }
            },
            '<' => {
                chars.next();
                if Some('<') == chars.peek().copied() {
                    res.push(Token::new(Tok::DLAngBr, line));
                    chars.next();
                } else if Some('=') == chars.peek().copied() {
                    res.push(Token::new(Tok::LABEq, line));
                    chars.next();
                } else {
                      res.push(Token::new(Tok::LAngBr, line));
                };

            },
            '>' => {
                chars.next();
                if Some('>') == chars.peek().copied() {
                        res.push(Token::new(Tok::DRAngBr, line));
                        chars.next();
                } else if Some('=') == chars.peek().copied() {
                        res.push(Token::new(Tok::RABEq, line));
                        chars.next();
                } else {
                      res.push(Token::new(Tok::RAngBr, line));
                };
            },
            ' ' | '\t' => {chars.next();},
            '\n' => {line += 1; chars.next();}
            'a'..='z' | 'A'..='Z' | '_' => {
                let mut idn = String::new();
                while let Some(ic) = chars.peek() {
                    //println!("{}", ic);
                    if ic.is_alphanumeric() || *ic == '_' {
                        idn.push(*ic);
                        chars.next();
                    } else {
                        break;
                    }
                };
                let t = match_symb_tok(&idn);
                res.push(Token::new(t, line));
            }
            '.' => {
                chars.next();
                if Some('.') == chars.peek().copied() {
                    res.push(Token::new(Tok::DoubleDot, line));
                    chars.next();
                } else {
                    res.push(Token::new(Tok::Dot, line));
                }
            }
            other => {
                panic!("{}: Unknown token {}", line, other);
            }
        }
    }

    
    res
}

pub fn try_combine(ch: &char, nextch: Option<char>, line: usize) -> Option<Token> {
    match (*ch, nextch) {
        ('+', Some('=')) => Some(Token::new(Tok::Combined(Box::new(Tok::Plus), Box::new(Tok::Equals)), line)),
        ('-', Some('=')) => Some(Token::new(Tok::Combined(Box::new(Tok::Minus), Box::new(Tok::Equals)), line)),
        ('*', Some('=')) => Some(Token::new(Tok::Combined(Box::new(Tok::Star), Box::new(Tok::Equals)), line)),
        ('/', Some('=')) => Some(Token::new(Tok::Combined(Box::new(Tok::Slash), Box::new(Tok::Equals)), line)),
        ('^', Some('=')) => Some(Token::new(Tok::Combined(Box::new(Tok::Caret), Box::new(Tok::Equals)), line)),
        ('&', Some('=')) => Some(Token::new(Tok::Combined(Box::new(Tok::Ampersand), Box::new(Tok::Equals)), line)),
        ('|', Some('=')) => Some(Token::new(Tok::Combined(Box::new(Tok::VerBar), Box::new(Tok::Equals)), line)),
        ('-', Some('>')) => Some(Token::new(Tok::Combined(Box::new(Tok::Minus), Box::new(Tok::RAngBr)), line)),
        (':', Some(':')) => Some(Token::new(Tok::Combined(Box::new(Tok::Colon), Box::new(Tok::Colon)), line)),


        other => None,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Kword {
    Let,
    True,
    False,
    If,
    Else,
    While,
    For,
    In,
    Break,
    Continue,
    Func,
    Return,
    Overload,
    Extern,
    Pub,
    Module,
    Struct,
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum Intrinsic {
    Print,
    Len,
}

fn match_symb_tok(word: &str) -> Tok {
    match word {
        "let" => Tok::Keyword(Kword::Let),
        "true" => Tok::Keyword(Kword::True),
        "false" => Tok::Keyword(Kword::False),
        "if" => Tok::Keyword(Kword::If),
        "else" => Tok::Keyword(Kword::Else),
        "printintrin" => Tok::Intrin(Intrinsic::Print),
        "while" => Tok::Keyword(Kword::While),
        "for" => Tok::Keyword(Kword::For),
        "in" => Tok::Keyword(Kword::In),
        "break" => Tok::Keyword(Kword::Break),
        "func" => Tok::Keyword(Kword::Func),
        "continue" => Tok::Keyword(Kword::Continue),
        "return" => Tok::Keyword(Kword::Return),
        "overload" => Tok::Keyword(Kword::Overload),
        "extern" => Tok::Keyword(Kword::Extern),
        "pub" => Tok::Keyword(Kword::Pub),
        "module" => Tok::Keyword(Kword::Module),
        "struct" => Tok::Keyword(Kword::Struct),
        "_len" => Tok::Intrin(Intrinsic::Len),
        other => Tok::Identifier(other.to_string()),
    }
}

