use std::collections::HashMap;
use std::fmt::Binary;

use crate::fcparse::fcparse::{self as fparse, AstRoot, BinaryOp, UnaryOp};
use crate::fcparse::fcparse::AstNode;
use crate::logger::logger::{ErrKind, LogLevel, Logger, WarnKind};
use crate::logger::logger as log;

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
                return Some((idx, v));
            };
        } 
        None
    }

    pub fn get_mut(&mut self, var_name: String) -> Option<(usize, &mut FSymbol)> {
        for (idx, scv) in self.st.iter_mut().enumerate() {
            if let Some(v) = scv.get_mut(&var_name) {
                return Some((idx, v));
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
    permissive: bool,
    parsing_loop: Vec<usize>, // fold level 
    func_table: HashMap<String, AstNode>,
}

impl SemAn {
    /// Inits semantic analyzer struct. Permissive flag for less type checks
    pub fn new(permissive: bool, functab: HashMap<String, AstNode>) -> SemAn {
        SemAn { 
            symb_table: SymbolTable::new(),
            cur_scope: 0,
            permissive: permissive,
            parsing_loop: Vec::new(),
            func_table: functab
        }
    }

    pub fn analyze(&mut self, ast: &Vec<AstRoot>, logger: &mut Logger) {
        if self.func_table.get("main").is_none() {
            logger.emit(LogLevel::Error(ErrKind::NoMain), 0);
        }

        for root in ast {
            self.analyze_expr(root, logger); 
        }
    }

    fn analyze_expr(&mut self, node: &AstRoot, logger: &mut Logger) -> ExprDat {
        let mut exprdat = ExprDat::new(FType::none);
        let line = node.line;
        match &node.node {
            AstNode::Assignment { name, val, ft } => {
                let rightdat = self.analyze_expr(
                    &AstRoot::new(*val.clone(), line), logger
                );
                
                if self.symb_table.get(name.clone()).is_some() {
                    logger.emit(LogLevel::Error(ErrKind::Redeclaration(name.to_owned())), line);
                };
                
                if *ft == FType::none {
                    logger.emit(LogLevel::Error(ErrKind::NoneTypeAssign(name.clone(), rightdat.ftype)), line);
                }
                if *ft != rightdat.ftype {
                    logger.emit(LogLevel::Error(ErrKind::MismatchedTypes(*ft, rightdat.ftype)), line);
                }

                self.symb_table.newsymb(FSymbol::new(name.to_owned(), VarPosition::None, *ft));
                exprdat.ftype = *ft;
            }
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
                    &AstRoot::new(*left.clone(), line), logger);
                let rightd = self.analyze_expr(
                    &AstRoot::new(*right.clone(), line), logger);

                let is_shift_op = (*op == BinaryOp::BitShiftLeft) || (*op == BinaryOp::BitShiftRight);
                
                if is_shift_op {
                    // For shift operations, right operand must be uint or pointer
                    let is_valid_shift_right_type = matches!(
                        rightd.ftype,
                        FType::uint | FType::heapptr
                    );
                    
                    if !is_valid_shift_right_type {
                        logger.emit(
                            LogLevel::Error(ErrKind::BitShiftRHSType(*op, rightd.ftype)),
                            line
                        );
                    }
                    // Note: left operand type doesn't need to match right operand for shifts
                } else {
                    // For non-shift operations, types must match
                    if leftd.ftype != rightd.ftype {
                        logger.emit(
                            LogLevel::Error(ErrKind::BinOpDifTypes(*op, leftd.ftype, rightd.ftype)),
                            line
                        );
                    }
                }

                if (leftd.ftype == FType::bool) && 
                    (*op == BinaryOp::Add || *op == BinaryOp::Substract || 
                    *op == BinaryOp::Multiply || *op == BinaryOp::Divide) {
                        logger.emit(LogLevel::Error(ErrKind::BoolBounds(*op)), line);
                }

                let is_cmp_op = SemAn::is_cmp_op(op);
                if is_cmp_op {
                    exprdat.ftype = FType::bool;
                } else {
                    exprdat.ftype = leftd.ftype;
                }
            }
            AstNode::UnaryOp { op, expr } => {
                let rdat = self.analyze_expr(&AstRoot::new(*expr.clone(), line), logger);
                exprdat.ftype = rdat.ftype;

                if (*op == UnaryOp::Negate) && 
                    !((exprdat.ftype == FType::float) || (exprdat.ftype == FType::int)) {
                        logger.emit(LogLevel::Error(ErrKind::NegateBounds(exprdat.ftype)), line);
                }
            }
            AstNode::Variable(var) => {
                exprdat.ftype = match self.symb_table.get(var.clone()) {
                    Some(v) => v.1.ftype,
                    None => {
                        logger.emit(LogLevel::Error(ErrKind::UndeclaredVar(var.to_owned())), line);
                        FType::none
                    }
                }
            }
            AstNode::Reassignment { name, newval } => {
                let symb_type = {
                    let entry = match self.symb_table.get(name.clone()) {
                        Some(en) => en,
                        None => {
                            logger.emit(LogLevel::Error(ErrKind::UndeclaredVar(name.clone())), line);
                            (0, &FSymbol::new(name.to_owned(), VarPosition::None, FType::none))
                        }
                    };
                    entry.1.ftype
                };
                let newval_data = self.analyze_expr(&newval, logger);
                if symb_type != newval_data.ftype {
                    logger.emit(LogLevel::Error(ErrKind::IncompatTypes(symb_type, newval_data.ftype)), line);
                }
            }
            AstNode::IfStatement { cond, if_true, if_false } => {
                let cond_an = self.analyze_expr(cond, logger);
                if cond_an.ftype != FType::bool {
                    let lerr = LogLevel::Error(ErrKind::IfStmtNotBool(cond_an.ftype));
                    let lwarn = LogLevel::Warning(log::WarnKind::IfStmtNotBool);
                    self.permissive_error(line, logger, lerr, lwarn);
                }
                
                self.analyze_expr(*&if_true, logger);
                if let Some(iff_root) = if_false {
                    self.analyze_expr(iff_root, logger);
                }
            }
            AstNode::VariableCast { name, target_type } => {
                // TODO: add some meaningful type checks here
                if self.symb_table.get(name.clone()).is_none() {
                    logger.emit(LogLevel::Error(ErrKind::UndeclaredVar(name.to_owned())), line);
                };

                exprdat.ftype = *target_type;
            }
            AstNode::Intrinsic { intr, val } => {
                let _ = self.analyze_expr(&AstRoot::new(*val.clone(), line), logger);
            }
            AstNode::CodeBlock { exprs } => {
                self.symb_table.enter_scope();
                for expr in exprs {
                    self.analyze_expr(expr, logger);
                }
                self.symb_table.exit_scope();
            }
            AstNode::WhileLoop { cond, body } => {
                self.parsing_loop.push(self.parsing_loop.len());

                let cond_dat = self.analyze_expr(&cond, logger);
                if cond_dat.ftype != FType::bool {
                    self.permissive_error(line, logger, 
                        LogLevel::Error(ErrKind::WhileLoopNotBool(cond_dat.ftype)), 
                        LogLevel::Warning(WarnKind::WhileLoopNotBool)
                    );
                }

                self.analyze_expr(&body, logger);

                self.parsing_loop.pop();
            }
            AstNode::ForLoop { itervar, iter_upd, iter_cond, body } => {
                self.parsing_loop.push(self.parsing_loop.len());
                self.symb_table.enter_scope();

                self.analyze_expr(&itervar, logger);
                self.analyze_expr(&iter_upd, logger);
                self.analyze_expr(&iter_cond, logger);
                self.analyze_expr(&body, logger);

                self.symb_table.exit_scope();
                self.parsing_loop.pop();
            }
            AstNode::BreakLoop => {
                if self.parsing_loop.len() == 0 {
                    logger.emit(LogLevel::Error(ErrKind::BreakNotLoop), line);
                }
            }
            AstNode::ContinueLoop => {
                if self.parsing_loop.len() == 0 {
                    logger.emit(LogLevel::Error(ErrKind::ContinueNotLoop), line);
                }
            }
            AstNode::Function { name, args, ret_type, body } => {
                self.analyze_expr(&AstRoot::new(*body.clone(), line), logger);
            }
   
            _ => {}
        }
        exprdat
    }

    /// Prints warning if permissive mode enabled, otherwise error
    fn permissive_error(&mut self, line: usize, logger: &mut Logger, lerr: LogLevel, lwarn: LogLevel) {
        if self.permissive {
            logger.emit(lwarn, line);
        } else {
            logger.emit(lerr, line);
        }
    }

    pub fn is_cmp_op(op: &BinaryOp) -> bool {
        matches!(*op, BinaryOp::Compare(_))
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
