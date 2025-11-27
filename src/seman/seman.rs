use std::collections::HashMap;

use crate::fcparse::fcparse::{self as fparse, AstRoot};
use crate::fcparse::fcparse::AstNode;

#[derive(Debug)]
pub struct FSymbol {
    pub name: String,
    pub cur_reg: usize,
    pub ftype: FType, 
}

impl FSymbol {
    pub fn new(n: String, reg: usize, ft: FType) -> FSymbol {
        FSymbol { name: n, cur_reg: reg, ftype: ft }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum FType {
    uint,
    int,
    float,
    bool,
    strconst,
    dsptr,
    heapptr,
    none
}

/// Semantic analyzer struct
#[derive(Debug)]
pub struct SemAn {
    symb_table: Vec<HashMap<String, FSymbol>>,
    cur_scope: usize,
}

impl SemAn {
    pub fn new() -> SemAn {
        SemAn { 
            symb_table: vec![HashMap::new()],
            cur_scope: 0,
        }
    }

    pub fn analyze(&mut self, ast: &Vec<AstRoot>) {
        for root in ast {
            self.analyze_expr(root); 
        }
    }

    fn analyze_expr(&mut self, node: &AstRoot) -> ExprDat {
        let mut exprdat = ExprDat::new(FType::none);
        let line = node.line;
        match &node.node {
            AstNode::Assignment { name, val, ft } => {
                let rightdat = self.analyze_expr(
                    &AstRoot::new(*val.clone(), line)
                );
                
                if let Some(_) = self.get_var(name.clone()) {
                    panic!("{}: redeclaration of variable `{}`", line, name);
                }; 

                self.newsymb(FSymbol::new(name.to_owned(), 0, *ft));
            }
            AstNode::EnterScope => {self.enter_scope();}
            AstNode::LeftScope => {self.exit_scope();}
   
            _ => {}
        }
        exprdat
    }

    fn get_var(&mut self, var_name: String) -> Option<(usize, &FSymbol)> {
        for (idx, scv) in self.symb_table.iter().enumerate() {
            if let Some(v) = scv.get(&var_name) {
                return Some((idx, v.clone()));
            };
        } 
        None
    }

    fn enter_scope(&mut self) {
        self.cur_scope += 1;
        self.symb_table.push(HashMap::new());
    }

    fn exit_scope(&mut self) {
        self.cur_scope -= 1;
        self.symb_table.pop();
    }

    fn newsymb(&mut self, fsymb: FSymbol) {
        self.symb_table
                .get_mut(self.cur_scope)
                .unwrap()
                .insert(fsymb.name.clone(), fsymb); 
    }
}

#[derive(Debug)]
pub struct ExprDat {
    ftype: FType,
}

impl ExprDat {
    pub fn new(ftype: FType) -> ExprDat {
        ExprDat { ftype: ftype }
    }
}
