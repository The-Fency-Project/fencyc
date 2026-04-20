use std::collections::{HashMap, HashSet};
use std::mem::discriminant;
use std::sync::{Arc, Mutex};
use std::sync::mpsc::Sender;


use indexmap::IndexMap;

use crate::cli::Target;
use crate::codegen::codegen::CodeGen;
use crate::fcparse::fcparse::{AstNode, Attr, FuncDat, GenericType, TraitInfo, TraitTable};
use crate::fcparse::fcparse::{AstRoot, BinaryOp, FuncArg, 
    FuncTable, UnaryOp};
use crate::lex::Intrinsic;
use crate::logger::logger::{self as log, LogMessage};
use crate::logger::logger::{ErrKind, LogLevel, WarnKind};

#[derive(Debug, Clone)]
pub struct FSymbol {
    pub name: String,
    pub cur_reg: VarPosition,
    pub ftype: FType,
    pub dsname: Option<String>,
    pub len: Option<usize>, // for arrays and strings
    pub owner: bool, // for ptrs: does symbol own memory
    pub moved: Option<usize>, // if was moved, on which line (moved val cant be used after)
}

impl FSymbol {
    pub fn new(n: String, pos: VarPosition, ft: FType) -> FSymbol {
        FSymbol {
            name: n,
            cur_reg: pos,
            ftype: ft,
            dsname: None,
            len: None,
            owner: false,
            moved: None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum FType {
    uint,
    int,
    double,
    bool,
    strconst,
    dsptr,
    heapptr,
    none,                       // No ftype!
    nil,                        // real voxvm thing! (good old times, now deprecated)
    Array(Box<FType>, usize), // type, count 
                                                          
    Struct(String),
    StructPtr(String),
    StructHeapPtr(String),
    ubyte,
    ibyte,
    u32,
    i32,
    single,
    any, // some kind of wildcard for seman 
    Ptr, 
    ushort,
    ishort,
    TypePtr(Box<FType>),

    Generic(String),
}

impl Into<qbe::Type> for FType {
    fn into(self) -> qbe::Type {
        match self {
            FType::int | FType::uint  => qbe::Type::Long,
            FType::double             => qbe::Type::Double,
            FType::single             => qbe::Type::Single,
            FType::u32 | FType::i32   => qbe::Type::Word,
            FType::bool | FType::ubyte | FType::ibyte 
                => qbe::Type::Word, // qbe assignment rule
            FType::Array(el, count)    => {
                Into::<qbe::Type>::into(*el)
            },
            FType::strconst | FType::StructPtr(_) | FType::StructHeapPtr(_) 
                => qbe::Type::Long, // ptr
            ref _other => todo!("Match ft qbf for {:?}", self)
        }
    }
}

impl PartialEq for FType {
    fn eq(&self, other: &Self) -> bool {
        self.is_compatible_with(other)
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

use std::fmt;

impl fmt::Display for FType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FType::uint => write!(f, "uint"),
            FType::int => write!(f, "int"),
            FType::double => write!(f, "double"),
            FType::bool => write!(f, "bool"),
            FType::strconst => write!(f, "strconst"),
            FType::dsptr => write!(f, "dsptr"),
            FType::heapptr => write!(f, "heapptr"),
            FType::none => write!(f, "none"),
            FType::nil => write!(f, "nil"),
            FType::Array(el, count) => {
                write!(f, "Array[{};{}]", el, count)
            }
            FType::Struct(name)        => write!(f, "s_{}", name),
            FType::StructPtr(name)     => write!(f, "ptr_{}", name),
            FType::StructHeapPtr(name) => write!(f, "h_{}", name),
            FType::ubyte      => write!(f, "ubyte"),
            FType::ibyte      => write!(f, "ibyte"),
            FType::u32        => write!(f, "u32"),
            FType::i32        => write!(f, "i32"),
            FType::single     => write!(f, "single"),
            FType::any        => write!(f, "any"),
            FType::Ptr        => write!(f, "Ptr"),
            FType::ushort     => write!(f, "ushort"),
            FType::ishort     => write!(f, "ishort"),
            FType::TypePtr(t) => write!(f, "*{}", t),
            FType::Generic(t) => write!(f, "generic type {}", t),
        }
    }
}

impl FType {
    fn is_compatible_with(&self, other: &FType) -> bool {
        match (self, other) {
            (_, FType::any) | (FType::any, _) => true,
            _ => discriminant(self) == discriminant(other),
        }
    }

    pub fn size(&self) -> u64 {
        CodeGen::match_ft_qbf_t(self, true).size()
    }

    /// Checks whether it is a struct type and if so returns name 
    pub fn if_struct(&self) -> Option<String> {
        match self {
            FType::Struct(st) | FType::StructPtr(st) | FType::StructHeapPtr(st) 
                => Some(st.clone()),
            _other => None,
        }
    }

    /// True for single and double types 
    pub fn is_float(&self) -> bool {
        match self {
            FType::single | FType::double => true,
            _ => false,
        }
    }

    pub fn is_numerical(&self) -> bool {
        match self {
            FType::uint | FType::u32 | FType::ushort | FType::ubyte => true,
            FType::int | FType::i32 | FType::ishort | FType::ibyte => true,
            other if other.is_float() => true,
            _ => false,
        }
    }

    /// Whether this type may be return type of main function 
    pub fn can_be_main_ret(&self) -> bool {
        match self {
            FType::none => true,
            other if other.is_numerical() && !other.is_float() => true,
            other => false,
        }
    }

    pub fn rm_prefix(s: &str) -> String {
        let mut res = s.to_owned();

        let prefixes = ["s_", "h_", "ptr_"];
        for p in prefixes {
            if let Some(stripped) = res.strip_prefix(p) {
                res = stripped.to_owned();
            };
        }

        res
    }
}

/// Deprecated
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
    // using indexmap to presave order for 
    // RAII
    st: Vec<IndexMap<String, FSymbol>>,
    pub cur_scope: usize,
}
impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            st: vec![IndexMap::new()],
            cur_scope: 0,
        }
    }

    pub fn enter_scope(&mut self) {
        self.cur_scope += 1;
        self.st.push(IndexMap::new());
    }

    /// Returns vec of dropped vals
    pub fn exit_scope(&mut self) -> Vec<FSymbol> {
        self.cur_scope -= 1;
        let mut res: Vec<FSymbol> = Vec::new();
        if let Some(mut poped) = self.st.pop() {
            for (_key, val) in poped.drain(..) {
                res.push(val);
            }
        };
        res
    }

    pub fn to_drop(&mut self) -> Vec<FSymbol> {
        let mut res: Vec<FSymbol> = Vec::new();
        if let Some(poped) = self.st.last() {
            for (_key, val) in poped {
                res.push(val.clone());
            }
        };
        res.reverse();
        res
    }

    pub fn newsymb(&mut self, fsymb: FSymbol) {
        self.st
            .get_mut(self.cur_scope)
            .unwrap()
            .insert(fsymb.name.clone(), fsymb);
    }

    pub fn get(&self, var_name: &str) -> Option<(usize, &FSymbol)> {
        for (idx, scv) in self.st.iter().enumerate() {
            if let Some(v) = scv.get(var_name) {
                return Some((idx, v));
            };
        }
        None
    }

    pub fn get_mut(&mut self, var_name: &str) -> Option<(usize, &mut FSymbol)> {
        for (idx, scv) in self.st.iter_mut().enumerate() {
            if let Some(v) = scv.get_mut(var_name) {
                return Some((idx, v));
            };
        }
        None
    }

    pub fn get_mut_in_scope(&mut self, name: &str, scope: usize) -> Option<&mut FSymbol> {
        self.st.get_mut(scope)?.get_mut(name)
    }

    pub fn push_funcargs(&mut self, fargs: Vec<FuncArg>) {
        for (_idx, fa) in fargs.iter().enumerate() {
            // varposition is obsolete
            let symb = FSymbol::new(
                fa.name.clone(), 
                VarPosition::None, 
                fa.ftype.clone()
            );
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
    func_table: Arc<FuncTable>,
    declared_parse: HashMap<String, usize>, // already declared function names and first occurance
    //lines to check redecl
    parsing_func: Option<(String, usize)>, // currently parsing function name and overload idx
    pub matched_overloads: OverloadTable, // call idx -> overload idx, ret type
    expect_type: FType,                    // for overloads matching and generics (in future)
    struct_tab: Arc<StructTable>,
    line: usize,
    in_impl: String,
    usedmods: Vec<String>, // paths to used modules 
    target: Target,
    traits: Arc<TraitTable>,
    in_generic: HashMap<String, GenericType>, // generic types if we're in generic func/struct 
}

impl SemAn {
    /// Inits semantic analyzer struct. Permissive flag for less type checks
    pub fn new(permissive: bool, functab: Arc<FuncTable>, fname: String, 
        struct_tab: Arc<StructTable>, tgt: Target, tt: Arc<TraitTable>) -> SemAn {
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
            module: "main".into(),
            struct_tab: struct_tab,
            line: 0,
            in_impl: String::new(),
            usedmods: Vec::new(),
            target: tgt,
            traits: tt,
            in_generic: HashMap::new(),
        }
    }

    fn get_use_paths(&mut self) -> Vec<String> {
        let mut res = Vec::new();
        res.push(self.module.clone());
        res.extend(self.usedmods.iter().cloned());
        res
    }

    pub fn analyze(&mut self, ast: Arc<Vec<AstRoot>>, logger: &Sender<LogMessage>) 
        -> Result<(), ()> {
        let paths = self.get_use_paths();
        match self.func_table.get_func("main", &paths) {
            Some(fv) => {
                if fv.len() > 1 {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::FewMains(fv.len())), 
                        0,
                        self.fname.clone()
                    ));
                } else if fv.len() == 1 {
                    match fv[0].ret_type.can_be_main_ret() {
                        true => {}
                        false => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::MainRetIncompat(
                                    fv[0].ret_type.clone()
                                )),
                                0,
                                self.fname.clone()
                            ));
                        }
                    }
                }
            }
            None => {
                //logger.emit(LogLevel::Error(ErrKind::NoMain), 0);
            }
        }

        for root_arc in ast.iter() {
            self.analyze_expr(root_arc, logger);
        }

        Ok(())
    }

    fn analyze_expr(&mut self, node: &AstRoot, logger: &Sender<LogMessage>) -> ExprDat {
        let mut exprdat = ExprDat::new(FType::none);
        let line = node.line;
        self.line = line;
        
        for attr in &node.attrs {
            match attr {
                Attr::Target(tgts) => {
                    if !tgts.contains(&self.target) {
                        return exprdat;
                    }
                }
                other => {}
            }
        }

        match &node.node {
            AstNode::Assignment { name, val, ft } => {
                self.expect_type = ft.clone();
                let rightdat = self.analyze_expr(&AstRoot::new(*val.clone(), line), logger);
                self.expect_type = FType::none;

                if self.symb_table.get(&name).is_some() {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::Redeclaration(name.to_owned())),
                        line,
                        self.fname.clone()
                    ));
                };
                let paths = self.get_use_paths();

                let res_ft = match ft {
                    FType::none => {
                        rightdat.ftype.clone()
                    }
                    ft if ft.if_struct().is_some() => {
                        let name = ft.if_struct().unwrap();
                        if let Some(si) = self.struct_tab.get(&name, &paths) {
                            if !si.public && !name.contains(&self.module) {
                                logger.send(LogMessage::new(
                                    LogLevel::Error(ErrKind::NotPubStruct(name.to_owned())),
                                    line,
                                    self.fname.clone()
                                ));                                
                            }
                        } else {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::UnknownStruct(name.to_owned())),
                                line,
                                self.fname.clone()
                            ));
                        }
                        ft.clone()
                    }
                    _other => {ft.clone()}
                };

                match (&res_ft, &rightdat.ftype) {
                    (FType::Array(ft1, c1), FType::Array(ft2, c2)) => {
                       if *ft1 != *ft2 {
                           logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::MismatchedTypes(
                                    res_ft.clone(), 
                                    rightdat.ftype.clone()
                                )),
                                line,
                                self.fname.clone()
                           ));
                       }
                    }
                    (other1, other2) => {
                        if other1 != other2 {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::MismatchedTypes(
                                    res_ft.clone(), 
                                    rightdat.ftype.clone()
                                )),
                                line,
                                self.fname.clone()
                            ));
                        }
                    }
                }

                self.symb_table
                    .newsymb(FSymbol::new(
                                name.to_owned(), 
                                VarPosition::None, 
                                res_ft.clone()
                            ));
                exprdat.ftype = res_ft.clone();
            }
            AstNode::Int(_iv) => {
                exprdat.ftype = FType::int;
            }
            AstNode::Uint(_uv) => {
                exprdat.ftype = FType::uint;
            }
            AstNode::Double(_fv) => {
                exprdat.ftype = FType::double;
            }
            AstNode::boolVal(_bv) => {
                exprdat.ftype = FType::bool;
            }
            AstNode::StringLiteral(_s) => {
                exprdat.ftype = FType::strconst;
            }
            AstNode::I32(_) => {
                exprdat.ftype = FType::i32;
            }
            AstNode::U32(_) => {
                exprdat.ftype = FType::u32;
            }
            AstNode::Single(_) => {
                exprdat.ftype = FType::single;
            }
            AstNode::Ishort(_) => {
                exprdat.ftype = FType::ishort;
            }
            AstNode::Ushort(_) => {
                exprdat.ftype = FType::ushort;
            }
            AstNode::Ubyte(_) => {
                exprdat.ftype = FType::ubyte;
            }
            AstNode::Ibyte(_) => {
                exprdat.ftype = FType::ibyte;
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
                            LogLevel::Error(ErrKind::BinOpDifTypes(
                                *op, 
                                leftd.ftype.clone(),
                                rightd.ftype.clone()
                            )),
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
                exprdat.ftype = rdat.ftype.clone();

                if *op == UnaryOp::Negate
                    && !matches!(
                        exprdat.ftype,
                        FType::double | FType::int | FType::single | FType::i32 | FType::ibyte
                    )
                {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::NegateBounds(
                            exprdat.ftype.clone()
                        )),
                        line,
                        self.fname.clone(),
                    ));
                }

                match *op {
                    UnaryOp::AddressOf => match rdat.ftype {
                        FType::Struct(s) => exprdat.ftype = FType::StructPtr(s),
                        other => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::NoStructAddress("Address Of".to_owned(), other)),
                                line,
                                self.fname.clone(),
                            ));
                        }
                    },
                    UnaryOp::Deref => match rdat.ftype {
                        FType::StructPtr(s) | FType::StructHeapPtr(s) 
                            => exprdat.ftype = FType::Struct(s),
                        other => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::NoStructAddress("Dereference".to_owned(), other)),
                                line,
                                self.fname.clone(),
                            ));
                        }
                    },
                    _ => {} 
                }
            }
            AstNode::Variable(var) => {
                let paths = self.get_use_paths();
                if let Some(_v) = self.struct_tab.get(var, &paths) {
                    exprdat.ftype = FType::Struct(var.to_owned());
                    return exprdat;
                }
    
                if self.func_table.get_func(var, &paths).is_some() {
                    // TODO: func type
                    return exprdat;
                }

                exprdat.var_name = Some(var.clone());
                self.chk_move(&mut logger.clone(), &var, &mut exprdat, line); 
            }
            AstNode::Reassignment { name, idx, newval } => {
                let val = self.analyze_expr(
                    &AstRoot::new(*name.clone(), line), 
                    &logger.clone()
                );
                let newval_data = self.analyze_expr(&newval, logger);
                match &newval_data.ftype {
                    FType::Struct(s) if newval_data.var_name.is_some() => {
                        self.try_move(
                            &mut logger.clone(),
                            &newval_data.var_name.unwrap(),
                            line
                        );
                    },
                    other => {}
                }
                let res_type: FType = match val.ftype {
                    FType::Array(el, count) if idx.is_some() => {
                        *el.clone()
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
                if let Some(var) = self.symb_table.get(&name) {
                    let var_ft = var.1.ftype.clone();
                    if var_ft == *target_type {
                        logger.send(LogMessage::new(
                            LogLevel::Warning(WarnKind::ConvSame(
                                var_ft.clone()
                            )), 
                            line,
                            self.fname.clone()
                        ));
                    }
                    self.chk_cast(&var_ft, target_type, logger.clone());
                } else {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::UndeclaredVar(name.to_owned())),
                        line,
                        self.fname.clone()
                    ));
                }

                exprdat.ftype = target_type.clone();
            }
            AstNode::Intrinsic { intr, val } => {
                let rdat = self.analyze_expr(&AstRoot::new(*val.clone(), line), logger);
                match intr {
                    Intrinsic::Len => {
                        match rdat.ftype {
                            FType::Array(el, count) => {},
                            FType::strconst => {},
                            other => {
                                logger.send(LogMessage::new(
                                    LogLevel::Error(
                                        ErrKind::MismatchedTypes(
                                            FType::Array(
                                                Box::new(FType::any), 
                                                0,
                                            ), 
                                            other
                                        )
                                    ),
                                    line,
                                    self.fname.clone()
                                ));
                            }
                        }
                        exprdat.ftype = FType::uint; 
                    },
                    Intrinsic::Sizeof => {
                        exprdat.ftype = FType::uint;
                    }
                    Intrinsic::BitsOf => {
                        exprdat.ftype = match rdat.ftype {
                            FType::single => FType::u32,
                            FType::double => FType::uint,
                            other => {
                                logger.send(LogMessage::new(
                                    LogLevel::Error(ErrKind::BitsCastErr(
                                        "_bitsof".into(),
                                        other,
                                        vec![FType::single, FType::double]
                                    )),
                                    self.line,
                                    self.fname.clone()
                                ));

                                return exprdat;
                            }
                        }
                    }
                    Intrinsic::FromBits => {
                        exprdat.ftype = match rdat.ftype {
                            FType::uint => FType::double,
                            FType::u32 => FType::single,
                            other => {
                                logger.send(LogMessage::new(
                                    LogLevel::Error(ErrKind::BitsCastErr(
                                        "_frombits".into(),
                                        other,
                                        vec![FType::u32, FType::uint]
                                    )),
                                    self.line,
                                    self.fname.clone()
                                ));

                                return exprdat;
                            }
                        };
                    }
                    _other => {}
                }
            }
            AstNode::CodeBlock { exprs } => {
                self.symb_table.enter_scope();
                for expr in exprs {
                    let ed = self.analyze_expr(expr, logger);
                    exprdat.has_returned = ed.has_returned;
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
                ret_type: _,
                body,
                public: _,
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

                let generics = name.get_generics();
                let generic_names = name.get_generic_names();

                for arg in args {
                    match &arg.ftype {
                        ft if ft.if_struct().is_some() => {
                            let name = ft.if_struct().unwrap();
                            let paths = self.get_use_paths();
                            if let Some(si) = self.struct_tab.get(&name, &paths) {
                                if !si.public && !name.contains(&self.module) {
                                    logger.send(LogMessage::new(
                                        LogLevel::Error(ErrKind::NotPubStruct(name.to_owned())),
                                        line,
                                        self.fname.clone()
                                    ));                                
                                }
                            } else {
                                let last_seg = name.rsplit("::").next().unwrap();
                                if !(generic_names.iter().any(|g| g == last_seg)) {
                                    logger.send(LogMessage::new(
                                        LogLevel::Error(ErrKind::UnknownStruct(name.to_owned())),
                                        line,
                                        self.fname.clone()
                                    ));
                                }
                            }
                        }
                        _other => {}
                    }
                }

                self.symb_table.enter_scope();
                self.symb_table.push_funcargs(args.to_vec());
                self.in_generic = generics.into_iter().map(|g| {
                    (g.name.clone(), g)
                }).collect();

                let fdat = self
                    .analyze_expr(&AstRoot::new(*body.clone(), line), logger);

                self.in_generic = HashMap::new();
                self.symb_table.exit_scope();
                self.parsing_func = None;

                if !fdat.has_returned {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::NoReturn()),
                        line,
                        self.fname.clone()
                    ));
                }
            }
            AstNode::ExternedFunc {
                name,
                args,
                ret_type: _,
                public: _,
                real_name: _,
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
            AstNode::FunctionOverload { func, idx, public: _ } => {
                self.parsing_func = Some(("".to_owned(), *idx));
                self.analyze_expr(&AstRoot::new(*func.clone(), line), logger);
            }
            AstNode::Call {
                func_name,
                args,
                idx,
            } => {
                let f_name_s = func_name.path_to_string();
                let paths = self.get_use_paths();

                // if we're inside generic
                let mut generic_f = None;
                let f_name_end = f_name_s.rsplit("::").next().unwrap();
                if let Some(v) = f_name_s.rsplit("::").nth(1) {
                    if let Some(g) = self.in_generic.get(v) {
                        for tb in &g.bounds {
                            if let Some(f) = self.traits.t.get(tb) {
                                if let Some(fdat) = f.req_funcs.get(f_name_end) {
                                    generic_f = Some(fdat.clone());
                                }
                            }
                        } 
                    }
                };


                let func_dat_vec = match self.func_table.get_func(
                    &func_name.path_to_string(), &paths) {
                    Some(v) => v.clone(),
                    None if generic_f.is_some() => {
                        vec![generic_f.unwrap().clone()]
                    }
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
                    let mut flag_matches: bool = true;
                    let mut extrn = false;
                    if overload.externed {
                        extrn = true;
                    }
                    
                    if overload.args.len() != args.len() {
                        continue;
                    }

                    let generics: HashMap<String, GenericType> = overload.name
                        .get_generics()
                        .iter()
                        .map(|e| {(e.name.clone(), e.clone())})
                        .collect();

                    for (idx, arg) in args.iter().enumerate() {
                        let argdat = self.analyze_expr(arg, logger); 

                        let arg_typename = format!("{}", overload.args[idx].ftype)
                            .rsplit("::").next().unwrap().to_owned();

                        let mut passed_typename = format!("{}", argdat.ftype);
                        passed_typename = FType::rm_prefix(&passed_typename);

                        if let Some(gt) = generics.get(&arg_typename) {
                            let empty = HashSet::new();
                            let passed_impls = self.traits.impls.get(
                                &passed_typename
                            ).unwrap_or(&empty);

                            for b in &gt.bounds {     
                                if passed_impls.get(b).is_none() {
                                    logger.send(LogMessage::new(
                                        LogLevel::Error(ErrKind::GenericFuncInimpl(
                                            f_name_s.clone(),
                                            b.to_owned(),
                                            argdat.ftype.clone()
                                        )),
                                        self.line,
                                        self.fname.clone()
                                    ));
                                } 
                            }
                            continue;
                        };
                                                                     
                        if !argdat.ftype
                                .is_compatible_with(&overload.args[idx].ftype) {
                            flag_matches = false;
                            break;
                        }
                        if self.expect_type != FType::none && self.expect_type != overload.ret_type
                        {
                            flag_matches = false;
                            break;
                        }
                    }
                    if flag_matches {
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
                            (ov_idx_op, overload.ret_type.clone())
                        );
                        exprdat.ftype = overload.ret_type.clone();
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
                
                let paths = self.get_use_paths();

                if let Some(curf) = &self.parsing_func {
                    if let Some(fv) = self.func_table.get_func(&curf.0, &paths) {
                        let f = &fv[curf.1];
                        if retval.ftype != f.ret_type {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::IncompatReturn(
                                    curf.0.to_owned(),
                                    f.ret_type.clone(),
                                    retval.ftype.clone(),
                                )),
                                line,
                                self.fname.clone()
                            ));
                        }
                        match retval.ftype {
                            FType::StructPtr(_) => {
                                logger.send(LogMessage::new(
                                    LogLevel::Warning(WarnKind::RawPtrRet(retval.ftype)),
                                    line,
                                    self.fname.clone()
                                ));
                            },
                            _other => {}
                        }
                    };
                    exprdat.has_returned = true;
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
                self.chk_cast(&expr.ftype, target_type, logger.clone());
                if &expr.ftype == target_type {
                    logger.send(LogMessage::new(
                        LogLevel::Warning(WarnKind::ConvSame(expr.ftype)), 
                        line,
                        self.fname.clone()
                    ));
                }

                exprdat.ftype = target_type.clone();
            }
            AstNode::Array(ft, nodes) => {
                for (idx, node) in nodes.iter().enumerate() {
                    if matches!(*node, AstNode::ArrRep(_)) {
                        continue;
                    }

                    let ndat = self.analyze_expr(&AstRoot::new(node.clone(), line), logger);
                    if ndat.ftype != *ft {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::IncompatArrType(ft.clone(),
                                                    ndat.ftype, idx)),
                            line,
                            self.fname.clone()
                        ));
                    }
                    if ndat.var_name.is_some() {
                        self.try_move(
                            &mut logger.clone(), 
                            ndat.var_name.as_ref().unwrap(),
                            line
                        ); 
                    }
                }

                //// Array(usize, usize, usize) = 9, // typeid, count, arridx
                exprdat.ftype = FType::Array(
                    Box::new(ft.clone()), 
                    nodes.len()
                );
            }
            AstNode::ArrayElem(arr, idx) => {
                let val_dat = self.analyze_expr(
                    &AstRoot::new(*arr.clone(), self.line), 
                    &mut logger.clone()
                );

                let elem_type = match val_dat.ftype {
                    FType::Array(ft, count)  => Some(*ft.clone()),
                    FType::strconst          => Some(FType::ubyte),
                    _other => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::NonArrIndex(_other)),
                            self.line,
                            self.fname.clone()
                        ));
                        return exprdat;
                    },
                };

                let idx_exprdat = self.analyze_expr(&idx, logger);
                if idx_exprdat.ftype != FType::uint {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::ArrIdxType(
                            format!("{:?}", arr), 
                            idx_exprdat.ftype
                        )),
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
                let _exprd = self.analyze_expr(node, &logger.clone());
                self.module = old_mod;

            }
            AstNode::StructCreate { name, field_vals } => {
                exprdat.ftype = FType::Struct(
                    name.path_to_string()
                );

                let struct_data = match self.struct_tab.tab
                    .get(&name.path_to_string()) {
                    Some(v) => v.clone(),
                    None => {
                        logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::UnknownStruct(
                                    name.path_to_string()
                                )), 
                                line, 
                                self.fname.clone()
                        ));
                        return exprdat;
                    }
                };
                if struct_data.attrs.contains(&Attr::Heap) {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::HeapOnlyStack(exprdat.ftype.clone())),
                        line,
                        self.fname.clone()
                    ));
                }

                if struct_data.fields.len() != field_vals.len() {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::MismatchFieldsCount(
                            struct_data.fields.len(),
                            field_vals.len()
                        )), 
                        line, 
                        self.fname.clone()
                    ));
                    return exprdat;
                }

                for (field_name, field_val) in field_vals {
                    let expected = struct_data.fields.get(field_name)
                        .unwrap();

                    let field_ed = self.analyze_expr(
                        &AstRoot::new(*field_val.clone(), line), 
                        &logger.clone()
                    );

                    match &expected.ftype {
                        FType::Array(el, ct) if (expected.ftype == field_ed.ftype)
                            && (*ct != 0) => {
                            if let Some(vn) = field_ed.var_name {
                                self.try_move(
                                    &mut logger.clone(),
                                    &vn,
                                    line
                                );
                            };
                        }
                        FType::Struct(snm) => {
                            if let Some(vn) = field_ed.var_name {
                                self.try_move(
                                    &mut logger.clone(),
                                    &vn,
                                    line
                                );
                            };
                        }
                        other if *other != field_ed.ftype => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::MismatchFieldsTypes(
                                    field_name.clone(), expected.ftype.clone(), field_ed.ftype
                                )), 
                                line, 
                                self.fname.clone()
                            ));

                        }
                        other => {}
                    }
                }
            }
            AstNode::StructFieldAddr { val, field_name } => {
                let expr = self.analyze_expr(val, &logger.clone());

                let struct_name = match expr.ftype {
                    FType::Struct(st) | FType::StructPtr(st) | FType::StructHeapPtr(st) 
                        => st.to_owned(),
                    other => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::NonStructField(
                                other
                            )),
                            line,
                            self.fname.clone()
                        ));
                        return exprdat;
                    }
                };

                let paths = self.get_use_paths();
                let struct_info = match self.struct_tab.get(&struct_name, &paths) {
                    Some(v) => v,
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::UnknownStruct(
                                struct_name.clone(),
                            )),
                            line,
                            self.fname.clone()
                        ));
                        return exprdat;
                    }
                };

                let field_info = match struct_info.fields.get(field_name) {
                    Some(v) => v,
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::NoField(
                                struct_name.clone(),
                                field_name.clone(),
                            )),
                            line,
                            self.fname.clone()
                        ));
                        return exprdat;
                    }
                };
                exprdat.ftype = field_info.ftype.clone();

                if !field_info.public && (self.in_impl != struct_name) {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::NotPubFieldAddr(field_name.to_owned())),
                        self.line,
                        self.fname.clone()
                    ));
                    return exprdat;
                }
            }
            AstNode::Structure { name, fields, public, attrs } => {
                for f in fields {
                    match f {
                        AstNode::StructField { name, ftype, public } => {
                            if let Some(sn) = ftype.if_struct() {
                                let paths = self.get_use_paths();
                                if self.struct_tab.get(&sn, &paths).is_none() {
                                    logger.send(LogMessage::new(
                                        LogLevel::Error(ErrKind::UnknownStruct(
                                            sn.to_owned()
                                        )),
                                        self.line,
                                        self.fname.clone()
                                    ));
                                }
                            };
                        } 
                        other => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::StructNonField(
                                    Box::new(other.clone())
                                )),
                                self.line,
                                self.fname.clone()
                            ));
                        }
                    } 
                }
            }
            AstNode::StructImpl { name, body, Trait } => {
                let old_mod = self.module.clone();
                self.module = name.path_to_string();
                
                self.in_impl = name.path_to_string();
                let _ed = self.analyze_expr(&*body, &logger.clone());
                if let Some(tp) = Trait {
                    self.verify_trait(
                        &name, 
                        &*body, 
                        &tp.path_to_string(), 
                        &mut logger.clone()
                    );
                }
                self.in_impl = String::new();

                self.module = old_mod; 
            }
            AstNode::MethodCall { name, args, idx } => {
                let first_arg = args.get(0).expect(&format!(
                    "{}: Expected self", self.line
                ));

                let var_name = match &first_arg.node {
                    AstNode::Variable(s) => s.clone(),
                    other => unreachable!("{:?}", other)
                };

                let ft = match self.symb_table.get(&var_name) {
                    Some(v) => v,
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::UndeclaredVar(var_name)),
                            self.line,
                            self.fname.clone(),
                        ));
                        return exprdat;
                    }
                };

                let self_ft = ft.1.ftype.clone();
                let struct_name = match self_ft.if_struct() {
                    Some(v) => v.to_owned(),
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::NotStructMethod(
                                    var_name.clone(), self_ft
                            )),
                            self.line,
                            self.fname.clone()
                        ));
                        return exprdat;
                    }
                };

                let func_name = format!("{}::{}", struct_name, name.path_to_string());

                let mut res_args = Vec::new();
                let first = match self_ft {
                    FType::StructHeapPtr(st) => {
                        AstRoot::new(
                            AstNode::VariableCast { 
                                name: var_name, 
                                target_type: FType::StructPtr(st) 
                            },
                            self.line
                        )
                    }
                    FType::Struct(st) => {
                        AstRoot::new(
                            AstNode::UnaryOp { 
                                op: UnaryOp::AddressOf, 
                                expr: Box::new(first_arg.node.clone())
                            },
                            self.line
                        )
                    }
                    other => first_arg.clone()
                };
                res_args.push(first);
                res_args.extend_from_slice(&args[1..]);

                let call_node = AstRoot::new(
                    AstNode::Call { 
                        func_name: Box::new(
                            AstNode::string_to_path(&func_name)
                        ), 
                        args: res_args, 
                        idx: *idx 
                    }, 
                    self.line
                );

                exprdat = self.analyze_expr(&call_node, &logger.clone());
            }
            AstNode::Usemod { name } => {
                let name_st = name.path_to_string();

                self.usedmods.push(name_st);
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

    pub fn verify_trait(&mut self, sname_n: &AstNode, bd: &AstRoot, traitname: &str,
        logger: &mut Sender<LogMessage>) {
        let sname = &sname_n.path_to_string();
        let trait_info = match self.traits.t.get(traitname) {
            Some(v) => v.clone(),
            None => {
                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::UnknownTrait(traitname.to_owned())),
                    self.line,
                    self.fname.clone()
                ));
                return;
            }
        };
        
        let generics = trait_info.path.get_generics();
        for g in generics {
            let empty = HashSet::new();
            let impls = self.traits.impls.get(sname)
                .unwrap_or(&empty);
            for b in g.bounds {
                if impls.get(&b).is_none() {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::SupertraitBoundUnsat(
                            sname.to_owned(),
                            traitname.to_owned(),
                            b.to_owned()
                        )),
                        self.line, 
                        self.fname.clone()
                    ));
                } 
            }
        }; 

        let exprs = match &bd.node {
            AstNode::CodeBlock { exprs } => exprs,
            other => {
                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::NotBlockBody(Box::new(other.clone()))),
                    self.line,
                    self.fname.clone()
                ));

                return;
            }
        };

        let mut implemented: HashMap<String, FuncDat> = HashMap::new();
        for e in exprs {
            match &e.node {
                AstNode::Function { name, args, ret_type, body, public } => {
                    let name_segs = name.path_to_segs();
                    let fdat = FuncDat::new_from_astn(&e.node)
                        .unwrap();
                    implemented.insert(
                        name_segs
                            .last()
                            .expect("Empty funcname")
                            .to_owned(), 
                        fdat
                    );
                }
                other => {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::NotFuncInImpl(Box::new(
                                    other.clone())
                                )),
                        e.line,
                        self.fname.clone()
                    ));
                }
            }
        }

        // si - struct implemented
        let mut inimpl = trait_info.req_funcs.clone();
        for (si_k, si_v) in implemented {
            if let Some(f) = inimpl.get(&si_k) {
                if f.args.len() != si_v.args.len() {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::TraitFuncArgsLen(
                            traitname.to_owned(),
                            si_k.clone(),
                            f.args.len(),
                            si_v.args.len()
                        )),
                        self.line,
                        self.fname.clone()
                    ));
                    continue;
                }

                // checking ret type compat 
                let msg = LogMessage::new(
                    LogLevel::Error(ErrKind::TraitRetTypeIncompat(
                        si_k.clone(),
                        traitname.to_owned(),
                        f.ret_type.clone(),
                        si_v.ret_type.clone(),
                    )),
                    self.line,
                    self.fname.clone()
                );
                if !self.check_gen_compat(
                    &trait_info,
                    &si_v.ret_type,
                    &f.ret_type, 
                    &mut logger.clone(), 
                    sname, 
                    msg
                ) {
                    continue;
                }

                // checking args compat 
                for (idx, fa) in f.args.iter().enumerate() {
                    let sa = si_v.args.get(idx).unwrap();
                    let msg = LogMessage::new(
                        LogLevel::Error(ErrKind::TraitFuncArgsIncompat(
                            f.name.path_to_segs().last().unwrap().to_owned(),
                            traitname.to_owned(),
                            fa.ftype.clone(), sa.ftype.clone()
                        )),
                        self.line,
                        self.fname.clone()
                    );
                    if !self.check_gen_compat(
                        &trait_info, 
                        &sa.ftype, 
                        &fa.ftype, 
                        &mut logger.clone(), 
                        sname, 
                        msg
                    ) {
                        continue;
                    }
                } 
                inimpl.remove(&si_k);
            } else {
                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::TraitUnknownFunc(
                        si_k.clone(), traitname.to_owned() 
                    )),
                    self.line,
                    self.fname.clone()
                ));
            };
        }

        if !inimpl.is_empty() {
            let names = inimpl.keys().map(|k| {
                k.to_owned()
            }).collect();

            logger.send(LogMessage::new(
                LogLevel::Error(ErrKind::TraitIncompleteImpl(
                    traitname.to_owned(),
                    names
                )),
                self.line,
                self.fname.clone()
            ));
        }
    }

    /// checks func args generic compatibility and returns true if everything is ok
    /// sa: provided ftype, fa: expected ftype 
    /// sname: struct name 
    /// msg: failure logger message
    fn check_gen_compat(&mut self, ti: &TraitInfo, sa: &FType, fa: &FType,
        logger: &mut Sender<LogMessage>, sname: &str, msg: LogMessage)
        -> bool {
        match (sa, fa) {
            (o1, o2) if o1.if_struct().is_some() && o2.if_struct().is_some() => {
                let o1_nm     = o1.if_struct().unwrap();
                let o2_nm     = o2.if_struct().unwrap();
                let o2_nm_lst = o2_nm.rsplit("::").next().unwrap();

                let gn = ti.path.get_generic_names();
                let gen_cond = (o1_nm == sname) && 
                    (gn.iter().any(|n| {n == o2_nm_lst}));

                if !(o1_nm == o2_nm || gen_cond) {
                    logger.send(msg); 
                    return false;
                }
            } 
            (o1, o2) if discriminant(o1) == discriminant(o2) => {} 
            (o1, o2) => {
                logger.send(msg); 
                return false;
            }
        }
        return true;
    }

    pub fn is_cmp_op(op: &BinaryOp) -> bool {
        matches!(*op, BinaryOp::Compare(_))
    }

    pub fn chk_cast(&mut self, from: &FType, to: &FType, logger: Sender<LogMessage>) {
        match (from, to) {
            (FType::Struct(st1), FType::Struct(st2)) |
            (FType::StructPtr(st1), FType::StructPtr(st2)) |
            (FType::StructHeapPtr(st1), FType::StructHeapPtr(st2)) | 
            (FType::StructPtr(st1), FType::StructHeapPtr(st2)) |
            (FType::StructHeapPtr(st1), FType::StructHeapPtr(st2))
            if st1 != st2 => {
                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::IllegalCast(
                        from.clone(), to.clone()
                    )),
                    self.line,
                    self.fname.clone(),
                ));
            }
            _other => {}
            
        }
    }

    pub fn has_trait(&mut self, struct_name: &str, trait_name: &str) -> bool {
        let traits = match self.traits.impls.get(struct_name) {
            Some(v) => v,
            None => {return false;}
        };
        traits.contains(trait_name)
    }

    fn chk_move(&mut self, logger: &mut Sender<LogMessage>, var: &str,
        exprdat: &mut ExprDat, line: usize) {

        let mut moved = None;
        (exprdat.ftype, moved) = match self.symb_table.get(var) {
            Some(v) => (v.1.ftype.clone(), v.1.moved),
            None => {
                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::UndeclaredVar(var.to_owned())),
                    line,
                    self.fname.clone()
                ));
                (FType::none, None)
            }
        };

        if let Some(stnm) = exprdat.ftype.if_struct() {
            if let Some(movline) = moved {
                let (has_clone,) = match self.traits.impls.get(&stnm) {
                    Some(tab) => (
                        tab.contains("std::mem::Clone".into()),
                    ),
                    None => (false,),
                };

                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::MovedValUse(
                        var.to_owned(),
                        exprdat.ftype.clone(),
                        movline,  
                        has_clone
                    )),
                    self.line,
                    self.fname.clone()
                ));
            }
        };
    }

    fn try_move(&mut self, logger: &mut Sender<LogMessage>, var: &str, line: usize) {
        let var_ref = match self.symb_table.get_mut(var) {
            Some(v) => v.1,
            None => {
                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::UndeclaredVar(var.to_owned())),
                    line,
                    self.fname.clone()
                ));
                return;
            }
        };

        if let Some(movline) = var_ref.moved {
            let stnm = match &var_ref.ftype {
                FType::Array(el, ct) if el.if_struct().is_some() => {
                    el.if_struct().unwrap()
                },    
                other if other.if_struct().is_some() => {
                    other.if_struct().unwrap()
                }
                other => "".into()
            };

            let (has_clone,) = match self.traits.impls.get(&stnm) {
                    Some(tab) => (
                        tab.contains("std::mem::Clone".into()),
                    ),
                    None => (false,),
                };

            logger.send(LogMessage::new(
                LogLevel::Error(ErrKind::MovedValUse(
                    var.to_owned(),
                    var_ref.ftype.clone(),
                    movline,  
                    has_clone
                )),
                self.line,
                self.fname.clone()
            ));
        }

        match &var_ref.ftype {
            FType::Struct(_) => {
               var_ref.moved = Some(line);
            }
            FType::Array(el, _) if matches!(**el, FType::Struct(_)) => {
                var_ref.moved = Some(line);
            }
            other => {}
        }
    }
}

#[derive(Debug)]
pub struct ExprDat {
    ftype: FType,
    has_returned: bool,
    var_name: Option<String>,
}

impl ExprDat {
    pub fn new(ftype: FType) -> ExprDat {
        ExprDat { 
            ftype: ftype,
            has_returned: false,
            var_name: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructInfo {
    pub name: String,
    pub fields: IndexMap<String, StructField>,
    pub size: usize, 
    pub max_alignment: usize,
    pub public: bool,
    pub attrs: Vec<Attr>,
}

impl StructInfo {
    pub fn from_astn(astn: &AstNode) -> StructInfo {
        match astn {
            AstNode::Structure { name, fields, public, attrs } => {
                let parsed_fields = Self::parse_ast_fields(fields);
                StructInfo {
                    name: name.path_to_string(),
                    fields: parsed_fields,
                    size: 0,
                    max_alignment: 1,
                    public: *public,
                    attrs: attrs.clone(),
                }
            }
            other => panic!("Internal: expected struct, found {:?}", other),
        }
    }

    fn parse_ast_fields(fields: &Vec<AstNode>) -> IndexMap<String, StructField> {
        let mut res: IndexMap<String, StructField> = IndexMap::new();

        for v in fields {
            match v {
                AstNode::StructField { name, ftype, public } => {
                    let entry = StructField {
                        name: name.clone(),
                        offset: 0,
                        ftype: ftype.clone(),
                        public: *public,
                    };
                    res.insert(name.clone(), entry);
                }
                other => panic!("Internal: expected struct field, found {:?}", other),
            }
        }

        res
    }

    fn align_up(offset: usize, align: usize) -> usize {
        (offset + align - 1) & !(align - 1)
    }

    fn alignment_of(ft: &FType) -> usize {
        match ft {
            FType::strconst | FType::int | FType::uint | FType::double 
                | FType::StructPtr(_) | FType::StructHeapPtr(_) | FType::Ptr => {
                8
            }
            FType::i32 | FType::u32 | FType::single => 4,
            FType::Array(el, _ctr) => {
                Self::alignment_of(&el)
            }
            FType::Struct(_usize) => {
                todo!()
            }
            FType::bool | FType::ubyte | FType::ibyte => 1,
            other => unimplemented!("alignment_of for {:?}", other)
        }
    }

    
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub offset: usize,
    pub ftype: FType,
    pub public: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LayoutMark {
    Visiting,
    Done,
}

#[derive(Debug, Clone)]
pub struct StructTable {
    pub tab: HashMap<String, StructInfo>,
}

impl StructTable {
    pub fn new() -> StructTable {
        StructTable { 
            tab: HashMap::new()
        }
    }

    pub fn get(&self, name: &str, usemods: &Vec<String>) -> Option<StructInfo> {
        if let Some(v) = self.tab.get(name) {
            return Some(v.clone())
        }; 
        for modnm in usemods {
            let nm = format!("{}::{}", modnm, name);
            if let Some(v) = self.tab.get(&nm) {
                return Some(v.clone());
            };
        }
        return None;
    }

    pub fn from_several(tabs: &Vec<StructTable>) -> StructTable {
        let mut res = StructTable::new();
        for v in tabs {
            res.tab.extend(v.tab.clone());
        }
        res
    }

    pub fn push_from_astn(&mut self, astn: &AstNode) {
        match astn {
            AstNode::Structure { name: _, fields: _, public: _, attrs } => {
                let _struct = StructInfo::from_astn(astn);
                self.tab.insert(_struct.name.clone(), _struct);
            }
            other => panic!("Internal: ast node {:?} isnt struct", other)
        }
    }

    pub fn recalc_layouts(&mut self) -> Result<(), String> {
        let names: Vec<String> = self.tab.keys().cloned().collect();
        let mut marks: HashMap<String, LayoutMark> = HashMap::new();

        for name in names {
            self.layout_struct(&name, &mut marks)?;
        }

        Ok(())
    }

    fn layout_struct(
        &mut self,
        name: &str,
        marks: &mut HashMap<String, LayoutMark>,
    ) -> Result<(usize, usize), String> {
        if matches!(marks.get(name), Some(LayoutMark::Done)) {
            let info = self.tab.get(name).unwrap();
            return Ok((info.size, info.max_alignment));
        }

        if matches!(marks.get(name), Some(LayoutMark::Visiting)) {
            return Err(format!("recursive by-value struct detected: `{}`", name));
        }

        marks.insert(name.to_string(), LayoutMark::Visiting);

        let fields_snapshot: Vec<(String, FType)> = {
            let info = self
                .tab
                .get(name)
                .ok_or_else(|| format!("unknown struct `{}`", name))?;

            info.fields
                .values()
                .map(|f| (f.name.clone(), f.ftype.clone()))
                .collect()
        };

        let mut offset = 0usize;
        let mut max_align = 1usize;
        let mut computed_offsets: Vec<(String, usize)> = Vec::with_capacity(fields_snapshot.len());

        for (field_name, ftype) in fields_snapshot {
            let (field_size, field_align) = self.type_layout(&ftype, marks)?;

            max_align = max_align.max(field_align);
            offset = Self::align_up(offset, field_align);
            computed_offsets.push((field_name, offset));
            offset += field_size;
        }

        let struct_size = Self::align_up(offset, max_align);

        let info = self.tab.get_mut(name).unwrap();
        for (field_name, off) in computed_offsets {
            if let Some(field) = info.fields.get_mut(&field_name) {
                field.offset = off;
            }
        }
        info.size = struct_size;
        info.max_alignment = max_align;

        marks.insert(name.to_string(), LayoutMark::Done);
        Ok((struct_size, max_align))
    }

    fn type_layout(
        &mut self,
        ft: &FType,
        marks: &mut HashMap<String, LayoutMark>,
    ) -> Result<(usize, usize), String> {
        match ft {
            FType::strconst | FType::int | FType::uint | FType::double
            | FType::StructPtr(_) | FType::StructHeapPtr(_) | FType::Ptr => Ok((8, 8)),

            FType::i32 | FType::u32 | FType::single => Ok((4, 4)),
            FType::bool | FType::ubyte | FType::ibyte => Ok((1, 1)),

            FType::Array(el, ct) => {
                let (elem_size, elem_align) = self.type_layout(el, marks)?;
                Ok((elem_size * *ct, elem_align))
            }

            FType::Struct(sn) => {
                self.layout_struct(&sn, marks)
            }

            other => Err(format!("layout not implemented for {:?}", other)),
        }
    }

    fn align_up(offset: usize, align: usize) -> usize {
        (offset + align - 1) & !(align - 1)
    }
}

pub struct SemanResult {
    fname: String,
    ast: Arc<AstRoot>,
    matched_overloads: Vec<OverloadTable>,
    has_error: bool,
}
