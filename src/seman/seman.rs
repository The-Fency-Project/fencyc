use std::collections::HashMap;

use crate::fcparse::fcparse::{self as fparse, AstRoot};
use crate::fcparse::fcparse::AstNode;

#[derive(Debug)]
pub struct FSymbol {
    pub name: String,
    pub cur_reg: VarPosition,
    pub ftype: FType, 
}

impl FSymbol {
    pub fn new(n: String, pos: VarPosition, ft: FType) -> FSymbol {
        FSymbol { name: n, cur_reg: pos, ftype: ft }
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

#[derive(Debug, Clone, Copy)]
pub enum VarPosition {
    Stack(usize), /// idx in stack 
    Register(usize), /// reg idx 
    None,
}

#[derive(Debug)]
pub struct SymbolTable { 
    st: Vec<HashMap<String, FSymbol>>,
    pub cur_scope: usize
}
impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable { 
            st: vec![HashMap::new()], 
            cur_scope: 0 
        }
    }

    pub fn enter_scope(&mut self) {
        self.cur_scope += 1;
        self.st.push(HashMap::new());
    }

    /// Returns vec of regpositions of dropped
    pub fn exit_scope(&mut self) -> Vec<VarPosition> {
        self.cur_scope -= 1;
        let mut res: Vec<VarPosition> = Vec::new();
        if let Some(poped) = self.st.pop() {
            for (key, val) in poped.iter() {
                res.push(val.cur_reg);
            }
        };
        res
    }

    pub fn newsymb(&mut self, fsymb: FSymbol) {
        self.st
                .get_mut(self.cur_scope)
                .unwrap()
                .insert(fsymb.name.clone(), fsymb); 
    }

    pub fn get(&self, var_name: String) -> Option<(usize, &FSymbol)> {
        for (idx, scv) in self.st.iter().enumerate() {
            if let Some(v) = scv.get(&var_name) {
                return Some((idx, v.clone()));
            };
        } 
        None
    }

    pub fn get_mut_in_scope(&mut self, name: &str, scope: usize) -> Option<&mut FSymbol> {
        self.st.get_mut(scope)?.get_mut(name)
    }

}

/// Semantic analyzer struct
#[derive(Debug)]
pub struct SemAn {
    symb_table: SymbolTable,
    cur_scope: usize,
}

impl SemAn {
    pub fn new() -> SemAn {
        SemAn { 
            symb_table: SymbolTable::new(),
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
                
                if let Some(_) = self.symb_table.get(name.clone()) {
                    panic!("{}: redeclaration of variable `{}`", line, name);
                };

                if *ft != rightdat.ftype {
                    panic!("{}: mismatched types\nExpected type {:?}, got {:?}",
                        line, ft, rightdat.ftype);
                }

                self.symb_table.newsymb(FSymbol::new(name.to_owned(), VarPosition::None, *ft));
                exprdat.ftype = *ft;
            }
            AstNode::EnterScope => {self.symb_table.enter_scope();}
            AstNode::LeftScope => {self.symb_table.exit_scope();}
            AstNode::Int(iv) => {
                exprdat.ftype = FType::int;
            }
            AstNode::Uint(uv) => {
                exprdat.ftype = FType::uint;
            }
            AstNode::Float(fv) => {
                exprdat.ftype = FType::float;
            }
            AstNode::boolVal(bv) => {
                exprdat.ftype = FType::bool;
            }
            AstNode::BinaryOp { op, left, right } => {
                let leftd = self.analyze_expr(
                    &AstRoot::new(*left.clone(), line));
                let rightd = self.analyze_expr(
                    &AstRoot::new(*right.clone(), line));

                if leftd.ftype != rightd.ftype {
                    panic!("\n{}: Binary op {:?} can't be applied with different types: {:?} and {:?}\n",
                        line, op, leftd.ftype, rightd.ftype);
                }
                exprdat.ftype = leftd.ftype;
            }
            AstNode::Variable(var) => {
                exprdat.ftype = match self.symb_table.get(var.clone()) {
                    Some(v) => v.1.ftype,
                    None => {
                        panic!("\n{}: Usage of undeclared variable {}\n",
                            line, var);
                    }
                }
            }
   
            _ => {}
        }
        exprdat
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
