use std::collections::{HashMap, HashSet};
use std::fmt::Binary;

use crate::fcparse::fcparse::AstNode;
use crate::fcparse::fcparse::{self as fparse, AstRoot, BinaryOp, FuncArg, 
    FuncTable, UnaryOp};
use crate::lex::Intrinsic;
use crate::logger::logger as log;
use crate::logger::logger::{ErrKind, LogLevel, Logger, WarnKind};

#[derive(Debug, Clone)]
pub struct FSymbol {
    pub name: String,
    pub cur_reg: VarPosition,
    pub ftype: FType,
    pub dsname: Option<String>,
}

impl FSymbol {
    pub fn new(n: String, pos: VarPosition, ft: FType) -> FSymbol {
        FSymbol {
            name: n,
            cur_reg: pos,
            ftype: ft,
            dsname: None,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
#[repr(usize)]
pub enum FType {
    uint = 0,
    int = 1,
    float = 2,
    bool = 3,
    strconst = 4,
    dsptr = 5,
    heapptr = 6,
    none = 7,                       // No ftype!
    nil = 8,                        // real voxvm thing!
    Array(usize, usize, usize) = 9, // typeid, count, arridx
}

pub fn idx_to_ftype(idx: usize) -> Option<FType> {
    match idx {
        0 => Some(FType::uint),
        1 => Some(FType::int),
        2 => Some(FType::float),
        3 => Some(FType::bool),
        4 => Some(FType::strconst),
        5 => Some(FType::dsptr),
        6 => Some(FType::heapptr),
        7 => Some(FType::none), // No ftype!
        8 => Some(FType::nil),  // real voxvm thing!
        _ => None,
    }
}

/// Rust's ADTs implementation is bullshit. Thus fency should have `enum as uint`
/// from the box
pub fn ftype_to_idx(ft: &FType) -> usize {
    match ft {
        FType::uint => 0,
        FType::int => 1,
        FType::float => 2,
        FType::bool => 3,
        FType::strconst => 4,
        FType::dsptr => 5,
        FType::heapptr => 6,
        FType::none => 7,
        FType::nil => 8,
        other => unimplemented!(),
        // FType::Array(_, _) => 9, 
    }
}

#[derive(Debug, Clone, Copy)]
pub enum VarPosition {
    Stack(usize),
    /// idx in stack
    Register(usize),
    /// reg idx
    None,
}

#[derive(Debug)]
pub struct SymbolTable {
    st: Vec<HashMap<String, FSymbol>>,
    pub cur_scope: usize,
}
impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            st: vec![HashMap::new()],
            cur_scope: 0,
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

    pub fn push_funcargs(&mut self, fargs: Vec<FuncArg>) {
        for (idx, fa) in fargs.iter().enumerate() {
            let symb = FSymbol::new(fa.name.clone(), VarPosition::Register(idx + 1), fa.ftype);
            self.newsymb(symb);
        }
    }
}

/// Semantic analyzer struct
#[derive(Debug)]
pub struct SemAn {
    symb_table: SymbolTable,
    cur_scope: usize,
    permissive: bool,
    parsing_loop: Vec<usize>, // fold level
    func_table: FuncTable,
    declared_parse: HashMap<String, usize>, // already declared function names and first occurance
    //lines to check redecl
    parsing_func: Option<(String, usize)>, // currently parsing function name and overload idx
    pub matched_overloads: HashMap<usize, usize>, // call idx -> overload idx
    expect_type: FType,                    // for overloads matching and generics (in future)
}

impl SemAn {
    /// Inits semantic analyzer struct. Permissive flag for less type checks
    pub fn new(permissive: bool, functab: FuncTable) -> SemAn {
        SemAn {
            symb_table: SymbolTable::new(),
            cur_scope: 0,
            permissive: permissive,
            parsing_loop: Vec::new(),
            func_table: functab,
            declared_parse: HashMap::new(),
            parsing_func: None,
            matched_overloads: HashMap::new(),
            expect_type: FType::none,
        }
    }

    pub fn analyze(&mut self, ast: &Vec<AstRoot>, logger: &mut Logger) {
        match self.func_table.get_func("main") {
            Some(fv) => {
                if fv.len() > 1 {
                    logger.emit(LogLevel::Error(ErrKind::FewMains(fv.len())), 0);
                }
            }
            None => {
                logger.emit(LogLevel::Error(ErrKind::NoMain), 0);
            }
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
                self.expect_type = *ft;
                let rightdat = self.analyze_expr(&AstRoot::new(*val.clone(), line), logger);
                self.expect_type = FType::none;

                if self.symb_table.get(name.clone()).is_some() {
                    logger.emit(
                        LogLevel::Error(ErrKind::Redeclaration(name.to_owned())),
                        line,
                    );
                };

                if *ft == FType::none {
                    logger.emit(
                        LogLevel::Error(ErrKind::NoneTypeAssign(name.clone(), rightdat.ftype)),
                        line,
                    );
                }

                match (*ft, rightdat.ftype) {
                    // TODO
                    //// Array(usize, usize, usize) = 9, // typeid, count, arridx
                    (FType::Array(fti1, c1, _), FType::Array(fti2, c2, _)) => {
                       if fti1 != fti2 {
                           logger.emit(
                               LogLevel::Error(ErrKind::MismatchedTypes(*ft, rightdat.ftype)),
                               line,
                           );
                       }
                    }
                    (other1, other2) => {
                        if other1 != other2 {
                            logger.emit(
                                LogLevel::Error(ErrKind::MismatchedTypes(*ft, rightdat.ftype)),
                                line,
                            );
                        }
                    }
                }

                self.symb_table
                    .newsymb(FSymbol::new(name.to_owned(), VarPosition::None, *ft));
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
            AstNode::StringLiteral(s) => {
                exprdat.ftype = FType::strconst;
            }
            AstNode::Array(fti, nodes) => {
                exprdat.ftype = FType::Array(ftype_to_idx(fti), nodes.len(), 0);
            }
            AstNode::BinaryOp { op, left, right } => {
                let leftd = self.analyze_expr(&AstRoot::new(*left.clone(), line), logger);
                let rightd = self.analyze_expr(&AstRoot::new(*right.clone(), line), logger);

                let is_shift_op =
                    (*op == BinaryOp::BitShiftLeft) || (*op == BinaryOp::BitShiftRight);

                if is_shift_op {
                    // For shift operations, right operand must be uint or pointer
                    let is_valid_shift_right_type =
                        matches!(rightd.ftype, FType::uint | FType::heapptr);

                    if !is_valid_shift_right_type {
                        logger.emit(
                            LogLevel::Error(ErrKind::BitShiftRHSType(*op, rightd.ftype)),
                            line,
                        );
                    }
                    // Note: left operand type doesn't need to match right operand for shifts
                } else {
                    // For non-shift operations, types must match
                    if leftd.ftype != rightd.ftype {
                        logger.emit(
                            LogLevel::Error(ErrKind::BinOpDifTypes(*op, leftd.ftype, rightd.ftype)),
                            line,
                        );
                    }
                }

                if (leftd.ftype == FType::bool)
                    && (*op == BinaryOp::Add
                        || *op == BinaryOp::Substract
                        || *op == BinaryOp::Multiply
                        || *op == BinaryOp::Divide)
                {
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

                if (*op == UnaryOp::Negate)
                    && !((exprdat.ftype == FType::float) || (exprdat.ftype == FType::int))
                {
                    logger.emit(LogLevel::Error(ErrKind::NegateBounds(exprdat.ftype)), line);
                }
            }
            AstNode::Variable(var) => {
                exprdat.ftype = match self.symb_table.get(var.clone()) {
                    Some(v) => v.1.ftype,
                    None => {
                        logger.emit(
                            LogLevel::Error(ErrKind::UndeclaredVar(var.to_owned())),
                            line,
                        );
                        FType::none
                    }
                }
            }
            AstNode::Reassignment { name, newval } => {
                let symb_type = {
                    let entry = match self.symb_table.get(name.clone()) {
                        Some(en) => en,
                        None => {
                            logger
                                .emit(LogLevel::Error(ErrKind::UndeclaredVar(name.clone())), line);
                            (
                                0,
                                &FSymbol::new(name.to_owned(), VarPosition::None, FType::none),
                            )
                        }
                    };
                    entry.1.ftype
                };
                let newval_data = self.analyze_expr(&newval, logger);
                if symb_type != newval_data.ftype {
                    logger.emit(
                        LogLevel::Error(ErrKind::IncompatTypes(symb_type, newval_data.ftype)),
                        line,
                    );
                }
            }
            AstNode::IfStatement {
                cond,
                if_true,
                if_false,
            } => {
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
                if let Some(var) = self.symb_table.get(name.clone()) {
                    if var.1.ftype == *target_type {
                        logger.emit(LogLevel::Warning(WarnKind::ConvSame(var.1.ftype)), line);
                    }
                } else {
                    logger.emit(
                        LogLevel::Error(ErrKind::UndeclaredVar(name.to_owned())),
                        line,
                    );
                }

                exprdat.ftype = *target_type;
            }
            AstNode::Intrinsic { intr, val } => {
                let rdat = self.analyze_expr(&AstRoot::new(*val.clone(), line), logger);
                match intr {
                    Intrinsic::Len => {
                        match rdat.ftype {
                            FType::Array(_, _, _) => {},
                            other => {
                                logger.emit(
                                    LogLevel::Error(
                                        ErrKind::MismatchedTypes(FType::Array(0, 0, 0), other)
                                    ),
                                    line
                                );
                            }
                        }
                        exprdat.ftype = FType::uint; 
                    },
                    other => {}
                }
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
                    self.permissive_error(
                        line,
                        logger,
                        LogLevel::Error(ErrKind::WhileLoopNotBool(cond_dat.ftype)),
                        LogLevel::Warning(WarnKind::WhileLoopNotBool),
                    );
                }

                self.analyze_expr(&body, logger);

                self.parsing_loop.pop();
            }
            AstNode::ForLoop {
                itervar,
                iter_upd,
                iter_cond,
                body,
            } => {
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
            AstNode::Function {
                name,
                args,
                ret_type,
                body,
            } => {
                let mut override_flag = false;
                if let Some(v) = &self.parsing_func {
                    self.parsing_func = Some((name.clone(), v.1));
                    override_flag = true;
                } else {
                    self.parsing_func = Some((name.clone(), 0));
                }

                if let Some(func_line) = self.declared_parse.get(name) {
                    if !override_flag {
                        logger.emit(
                            LogLevel::Error(ErrKind::FuncRedecl(name.clone(), *func_line)),
                            line,
                        );
                    }
                } else {
                    self.declared_parse.insert(name.clone(), line);
                }

                if args.len() > 30 {
                    logger.emit(
                        LogLevel::Error(ErrKind::MuchDeclArgs(name.clone(), args.len())),
                        line,
                    );
                }

                self.symb_table.enter_scope();
                self.symb_table.push_funcargs(args.to_vec());

                self.analyze_expr(&AstRoot::new(*body.clone(), line), logger);

                self.symb_table.exit_scope();
                self.parsing_func = None;
            }
            AstNode::FunctionOverload { func, idx } => {
                self.parsing_func = Some(("".to_owned(), *idx));
                self.analyze_expr(&AstRoot::new(*func.clone(), line), logger);
            }
            AstNode::Call {
                func_name,
                args,
                idx,
            } => {
                let func_dat_vec = match self.func_table.get_func(func_name) {
                    Some(v) => v.clone(),
                    None => {
                        logger.emit(
                            LogLevel::Error(ErrKind::UndeclaredFunc(func_name.clone())),
                            line,
                        );
                        return exprdat;
                    }
                };
                for (over_idx, overload) in func_dat_vec.iter().enumerate() {
                    let mut flag: bool = true;
                    for (idx, arg) in args.iter().enumerate() {
                        let argdat = self.analyze_expr(arg, logger); // TODO: get this invariant
                                                                     // out of loop
                        if argdat.ftype != overload.args[idx].ftype {
                            flag = false;
                            break;
                        }
                        if self.expect_type != FType::none && self.expect_type != overload.ret_type
                        {
                            flag = false;
                            break;
                        }
                    }
                    if flag {
                        self.matched_overloads.insert(*idx, over_idx);
                        exprdat.ftype = overload.ret_type;
                        return exprdat;
                    }
                }

                logger.emit(
                    LogLevel::Error(ErrKind::FuncArgsTypeIncompat(func_name.clone())),
                    line,
                );
            }
            AstNode::ReturnVal { val } => {
                let retval = self.analyze_expr(&*val, logger);

                if let Some(curf) = &self.parsing_func {
                    if let Some(fv) = self.func_table.get_func(&curf.0) {
                        let f = &fv[curf.1];
                        if retval.ftype != f.ret_type {
                            logger.emit(
                                LogLevel::Error(ErrKind::IncompatReturn(
                                    curf.0.to_owned(),
                                    f.ret_type,
                                    retval.ftype,
                                )),
                                line,
                            );
                        }
                    };
                } else {
                    logger.emit(LogLevel::Error(ErrKind::ReturnOutOfFunc), line);
                };
            }
            AstNode::ExprCast { expr, target_type } => {
                let expr = self.analyze_expr(&AstRoot::new(*expr.clone(), line), logger);
                if expr.ftype == *target_type {
                    logger.emit(LogLevel::Warning(WarnKind::ConvSame(expr.ftype)), line);
                }

                exprdat.ftype = *target_type;
            }
            AstNode::Array(ft, nodes) => {
                for (idx, node) in nodes.iter().enumerate() {
                    let ndat = self.analyze_expr(&AstRoot::new(node.clone(), line), logger);
                    if ndat.ftype != *ft {
                        logger.emit(
                            LogLevel::Error(ErrKind::IncompatArrType(*ft, ndat.ftype, idx)),
                            line,
                        );
                    }
                }
                let ft_idx = ftype_to_idx(ft);

                // TODO
                //// Array(usize, usize, usize) = 9, // typeid, count, arridx
                exprdat.ftype = FType::Array(ft_idx, nodes.len(), 0 );
            }
            AstNode::ArrayElem(arr_name, idx) => {
                let array_symb = match self.symb_table.get(arr_name.clone()) {
                    Some(v) => v.clone().1,
                    None => {
                        logger.emit(
                            LogLevel::Error(ErrKind::UndeclaredVar(arr_name.to_owned())),
                            line,
                        );
                        return exprdat;
                    }
                };

                // TODO
                let elem_type = match array_symb.ftype {
                    FType::Array(fti, _, _) => idx_to_ftype(fti),
                    other => unreachable!(),
                };

                let idx_exprdat = self.analyze_expr(&idx, logger);
                if idx_exprdat.ftype != FType::uint {
                    logger.emit(
                        LogLevel::Error(ErrKind::ArrIdxType(arr_name.clone(), idx_exprdat.ftype)),
                        line,
                    );
                }

                let el_type_u = match elem_type {
                    Some(v) => v,
                    None => {
                        logger.emit(
                            LogLevel::Error(ErrKind::Internal("Can't match type".to_owned())),
                            line,
                        );
                        return exprdat;
                    }
                };

                exprdat.ftype = el_type_u;
            }
            _ => {}
        }
        exprdat
    }

    /// Prints warning if permissive mode enabled, otherwise error
    fn permissive_error(
        &mut self,
        line: usize,
        logger: &mut Logger,
        lerr: LogLevel,
        lwarn: LogLevel,
    ) {
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
