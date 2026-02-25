use std::collections::{HashMap, HashSet};
use std::fmt::Binary;
use std::sync::mpsc::Sender;

use crate::codegen::codegen::FuncData;
use crate::fcparse::fcparse::AstNode;
use crate::fcparse::fcparse::{self as fparse, AstRoot, BinaryOp, FuncArg, 
    FuncTable, UnaryOp};
use crate::lex::Intrinsic;
use crate::logger::logger::{self as log, LogMessage};
use crate::logger::logger::{ErrKind, LogLevel, Logger, WarnKind};

#[derive(Debug, Clone)]
pub struct FSymbol {
    pub name: String,
    pub cur_reg: VarPosition,
    pub ftype: FType,
    pub dsname: Option<String>,
    pub len: Option<usize>, // for arrays and strings
}

impl FSymbol {
    pub fn new(n: String, pos: VarPosition, ft: FType) -> FSymbol {
        FSymbol {
            name: n,
            cur_reg: pos,
            ftype: ft,
            dsname: None,
            len: None,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
#[repr(usize)]
pub enum FType {
    uint = 0,
    int = 1,
    double = 2,
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
        2 => Some(FType::double),
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
        FType::double => 2,
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
            // varposition is obsolete
            let symb = FSymbol::new(fa.name.clone(), VarPosition::None, fa.ftype);
            self.newsymb(symb);
        }
    }
}

pub type OverloadTable = HashMap<usize, (Option<usize>, FType)>;

/// Semantic analyzer struct
#[derive(Debug)]
pub struct SemAn {
    symb_table: SymbolTable,
    fname: String,
    cur_scope: usize,
    module: String,
    permissive: bool,
    parsing_loop: Vec<usize>, // fold level
    func_table: FuncTable,
    declared_parse: HashMap<String, usize>, // already declared function names and first occurance
    //lines to check redecl
    parsing_func: Option<(String, usize)>, // currently parsing function name and overload idx
    pub matched_overloads: OverloadTable, // call idx -> overload idx, ret type
    expect_type: FType,                    // for overloads matching and generics (in future)
}

impl SemAn {
    /// Inits semantic analyzer struct. Permissive flag for less type checks
    pub fn new(permissive: bool, functab: FuncTable, fname: String) -> SemAn {
        SemAn {
            symb_table: SymbolTable::new(),
            cur_scope: 0,
            permissive: permissive,
            parsing_loop: Vec::new(),
            func_table: functab,
            fname: fname,
            declared_parse: HashMap::new(),
            parsing_func: None,
            matched_overloads: HashMap::new(),
            expect_type: FType::none,
            module: "main".to_owned()
        }
    }

    pub fn analyze(&mut self, ast: &Vec<AstRoot>, logger: &Sender<LogMessage>) 
        -> Result<(), ()> {
        match self.func_table.get_func("main") {
            Some(fv) => {
                if fv.len() > 1 {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::FewMains(fv.len())), 
                        0,
                        self.fname.clone()
                    ));
                }
            }
            None => {
                //logger.emit(LogLevel::Error(ErrKind::NoMain), 0);
            }
        }

        for root in ast {
            self.analyze_expr(root, logger);
        }

        Ok(())
    }

    fn analyze_expr(&mut self, node: &AstRoot, logger: &Sender<LogMessage>) -> ExprDat {
        let mut exprdat = ExprDat::new(FType::none);
        let line = node.line;
        match &node.node {
            AstNode::Assignment { name, val, ft } => {
                self.expect_type = *ft;
                let rightdat = self.analyze_expr(&AstRoot::new(*val.clone(), line), logger);
                self.expect_type = FType::none;

                if self.symb_table.get(name.clone()).is_some() {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::Redeclaration(name.to_owned())),
                        line,
                        self.fname.clone()
                    ));
                };

                if *ft == FType::none {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::NoneTypeAssign(name.clone(), rightdat.ftype)),
                        line,
                        self.fname.clone()
                    ));
                }

                match (*ft, rightdat.ftype) {
                    // TODO
                    //// Array(usize, usize, usize) = 9, // typeid, count, arridx
                    (FType::Array(fti1, c1, _), FType::Array(fti2, c2, _)) => {
                       if fti1 != fti2 {
                            println!("here");
                           logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::MismatchedTypes(*ft, rightdat.ftype)),
                                line,
                                self.fname.clone()
                           ));
                       }
                    }
                    (other1, other2) => {
                        if other1 != other2 {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::MismatchedTypes(*ft, rightdat.ftype)),
                                line,
                                self.fname.clone()
                            ));
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
            AstNode::Double(fv) => {
                exprdat.ftype = FType::double;
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
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::BitShiftRHSType(*op, rightd.ftype)),
                            line,
                            self.fname.clone()
                        ));
                    }
                    // Note: left operand type doesn't need to match right operand for shifts
                } else {
                    // For non-shift operations, types must match
                    if leftd.ftype != rightd.ftype {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::BinOpDifTypes(*op, leftd.ftype, rightd.ftype)),
                            line,
                            self.fname.clone()
                        ));
                    }
                }

                if (leftd.ftype == FType::bool)
                    && (*op == BinaryOp::Add
                        || *op == BinaryOp::Substract
                        || *op == BinaryOp::Multiply
                        || *op == BinaryOp::Divide)
                {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::BoolBounds(*op)), 
                        line,
                        self.fname.clone()
                    ));
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
                    && !((exprdat.ftype == FType::double) || (exprdat.ftype == FType::int))
                {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::NegateBounds(exprdat.ftype)),
                        line,
                        self.fname.clone()
                    ));
                }
            }
            AstNode::Variable(var) => {
                exprdat.ftype = match self.symb_table.get(var.clone()) {
                    Some(v) => v.1.ftype,
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::UndeclaredVar(var.to_owned())),
                            line,
                            self.fname.clone()
                        ));
                        FType::none
                    }
                }
            }
            AstNode::Reassignment { name, idx, newval } => {
                let symb_type = {
                    let entry = match self.symb_table.get(name.clone()) {
                        Some(en) => en,
                        None => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::UndeclaredVar(name.clone())), 
                                line,
                                self.fname.clone()
                            ));
                            (
                                0,
                                &FSymbol::new(name.to_owned(), VarPosition::None, FType::none),
                            )
                        }
                    };
                    entry.1.ftype
                };
                let newval_data = self.analyze_expr(&newval, logger);
                let res_type: FType = match symb_type {
                    FType::Array(el_ft, _, _) if idx.is_some() => {
                        idx_to_ftype(el_ft).unwrap_or(FType::nil)
                    }
                    other => other
                };
                if res_type != newval_data.ftype {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::IncompatTypes(res_type, newval_data.ftype)),
                        line,
                        self.fname.clone()
                    ));
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
                    self.permissive_error(line, logger.clone(), lerr, lwarn);
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
                        logger.send(LogMessage::new(
                            LogLevel::Warning(WarnKind::ConvSame(var.1.ftype)), 
                            line,
                            self.fname.clone()
                        ));
                    }
                } else {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::UndeclaredVar(name.to_owned())),
                        line,
                        self.fname.clone()
                    ));
                }

                exprdat.ftype = *target_type;
            }
            AstNode::Intrinsic { intr, val } => {
                let rdat = self.analyze_expr(&AstRoot::new(*val.clone(), line), logger);
                match intr {
                    Intrinsic::Len => {
                        match rdat.ftype {
                            FType::Array(_, _, _) => {},
                            FType::strconst => {},
                            other => {
                                logger.send(LogMessage::new(
                                    LogLevel::Error(
                                        ErrKind::MismatchedTypes(FType::Array(0, 0, 0), other)
                                    ),
                                    line,
                                    self.fname.clone()
                                ));
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
                        logger.clone(),
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
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::BreakNotLoop), 
                        line,
                        self.fname.clone()
                    ));
                }
            }
            AstNode::ContinueLoop => {
                if self.parsing_loop.len() == 0 {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::ContinueNotLoop), 
                        line,
                        self.fname.clone()
                    ));
                }
            }
            AstNode::Function {
                name,
                args,
                ret_type,
                body,
                public,
            } => {
                let mut override_flag = false;
                if let Some(v) = &self.parsing_func {
                    self.parsing_func = Some((name.path_to_string(), v.1));
                    override_flag = true;
                } else {
                    self.parsing_func = Some((name.path_to_string(), 0));
                }

                if let Some(func_line) = self.declared_parse.get(&name.path_to_string()) {
                    if !override_flag {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::FuncRedecl(name.path_to_string(),
                                *func_line)),
                            line,
                            self.fname.clone()
                        ));
                    }
                } else {
                    self.declared_parse.insert(name.path_to_string(), line);
                }

                self.symb_table.enter_scope();
                self.symb_table.push_funcargs(args.to_vec());

                self.analyze_expr(&AstRoot::new(*body.clone(), line), logger);

                self.symb_table.exit_scope();
                self.parsing_func = None;
            }
            AstNode::ExternedFunc {
                name,
                args,
                ret_type,
                public
            } => {
                let mut override_flag = false;
                if let Some(v) = &self.parsing_func {
                    self.parsing_func = Some((name.path_to_string(), v.1));
                    override_flag = true;
                } else {
                    self.parsing_func = Some((name.path_to_string(), 0));
                }

                if let Some(func_line) = self.declared_parse.get(&name.path_to_string()) {
                    if !override_flag {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::FuncRedecl(name.path_to_string(),
                                *func_line)),
                            line,
                            self.fname.clone()
                        ));
                    }
                } else {
                    self.declared_parse.insert(name.path_to_string(), line);
                }

                self.symb_table.enter_scope();
                self.symb_table.push_funcargs(args.to_vec());

                self.symb_table.exit_scope();
                self.parsing_func = None;
            }
            AstNode::FunctionOverload { func, idx, public } => {
                self.parsing_func = Some(("".to_owned(), *idx));
                self.analyze_expr(&AstRoot::new(*func.clone(), line), logger);
            }
            AstNode::Call {
                func_name,
                args,
                idx,
            } => {
                let func_dat_vec = match self.func_table.get_func(
                    &func_name.path_to_string()) {
                    Some(v) => v.clone(),
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::UndeclaredFunc(
                                func_name.path_to_string()
                            )),
                            line,
                            self.fname.clone()
                        ));
                        return exprdat;
                    }
                };
                for (over_idx, overload) in func_dat_vec.iter().enumerate() {
                    let mut flag: bool = true;
                    let mut extrn = false;
                    if overload.externed {
                        extrn = true;
                    }

                    for (idx, arg) in args.iter().enumerate() {
                        let argdat = self.analyze_expr(arg, logger); // TODO: get this invariant
                                                                     // out of loop
                        if (overload.args.len() != args.len()) 
                                || argdat.ftype != overload.args[idx].ftype {
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
                        let ov_idx_op = if extrn {
                            None
                        } else {
                            Some(over_idx)
                        };
                       
                        let funame = func_name.path_to_string();
                        let ov_module = match funame.rfind("::") {
                            Some(pos) => funame[..pos].to_owned(),
                            None => funame.to_owned(), 
                        };
                        let same_mod = self.module == ov_module;
                        
                        if !overload.public && !same_mod {
                            // TODO: also iterate overloads till we find public one
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::NotPub(func_name.path_to_string())),
                                line,
                                self.fname.clone()
                            ));
                            return exprdat;
                        } 
                        self.matched_overloads.insert(*idx, 
                            (ov_idx_op, overload.ret_type)
                        );
                        exprdat.ftype = overload.ret_type;
                        return exprdat;
                    }
                }

                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::FuncArgsTypeIncompat(func_name.path_to_string())),
                    line,
                    self.fname.clone()
                ));
            }
            AstNode::ReturnVal { val } => {
                let retval = self.analyze_expr(&*val, logger);

                if let Some(curf) = &self.parsing_func {
                    if let Some(fv) = self.func_table.get_func(&curf.0) {
                        let f = &fv[curf.1];
                        if retval.ftype != f.ret_type {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::IncompatReturn(
                                    curf.0.to_owned(),
                                    f.ret_type,
                                    retval.ftype,
                                )),
                                line,
                                self.fname.clone()
                            ));
                        }
                    };
                } else {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::ReturnOutOfFunc), 
                        line,
                        self.fname.clone()
                    ));
                };
            }
            AstNode::ExprCast { expr, target_type } => {
                let expr = self.analyze_expr(&AstRoot::new(*expr.clone(), line), logger);
                if expr.ftype == *target_type {
                    logger.send(LogMessage::new(
                        LogLevel::Warning(WarnKind::ConvSame(expr.ftype)), 
                        line,
                        self.fname.clone()
                    ));
                }

                exprdat.ftype = *target_type;
            }
            AstNode::Array(ft, nodes) => {
                for (idx, node) in nodes.iter().enumerate() {
                    let ndat = self.analyze_expr(&AstRoot::new(node.clone(), line), logger);
                    if ndat.ftype != *ft {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::IncompatArrType(*ft, ndat.ftype, idx)),
                            line,
                            self.fname.clone()
                        ));
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
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::UndeclaredVar(arr_name.to_owned())),
                            line,
                            self.fname.clone()
                        ));
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
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::ArrIdxType(arr_name.clone(), idx_exprdat.ftype)),
                        line,
                        self.fname.clone()
                    ));
                }

                let el_type_u = match elem_type {
                    Some(v) => v,
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::Internal("Can't match type".to_owned())),
                            line,
                            self.fname.clone()
                        ));
                        return exprdat;
                    }
                };

                exprdat.ftype = el_type_u;
            }
            AstNode::Module { name, node } => {
                let old_mod = self.module.clone();
                self.module = match old_mod.as_str() {
                    "main" => name.clone(),
                    other => format!("{}::{}", other, name),
                };
                let exprd = self.analyze_expr(node, &logger.clone());
                self.module = old_mod;

            }
            _ => {}
        }
        exprdat
    }

    /// Prints warning if permissive mode enabled, otherwise error
    fn permissive_error(
        &mut self,
        line: usize,
        logger: Sender<LogMessage>,
        lerr: LogLevel,
        lwarn: LogLevel,
    ) {
        if self.permissive {
            logger.send(LogMessage::new(lwarn, line, self.fname.clone()));
        } else {
            logger.send(LogMessage::new(lerr, line, self.fname.clone()));
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
