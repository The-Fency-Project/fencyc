use std::collections::{HashMap, HashSet};
use std::mem::discriminant;
use std::sync::{Arc, Mutex};
use std::sync::mpsc::Sender;


use indexmap::IndexMap;

use crate::cli::Target;
use crate::codegen::codegen::CodeGen;
use crate::codegen::mirtoqbe;
 use crate::fcparse::fcparse::{self as fparse, AstNode, Attr, FuncDat, GenericType, MatchPattern, TraitInfo, TraitTable};
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq)]
pub enum FType {
    uint,
    Usize,
    int,
    double,
    bool,
    strconst,
    dsptr,
    heapptr,
    none,                       // No ftype!
    nil,                        // real voxvm thing! (good old times, now deprecated)
    Array(Box<FType>, usize), // type, count 
                                                          
    Struct(String),       // owning by-value aggregate; destructive move
    StructPtr(String),    // non-owning safe raw pointer; trivial copy
    StructHeapPtr(String),// owning heap pointer; destructive move
    ubyte,
    ibyte,
    u32,
    i32,
    single,
    any, // some kind of wildcard for seman 
    Ptr,                  // non-owning FFI pointer; trivial copy
    ushort,
    ishort,
    TypePtr(Box<FType>),

    Generic(String),
    Function(Vec<FType>, Box<FType>),
    // Declaration-only tail. `none` denotes an untyped C variadic tail.
    Variadic(Box<FType>),
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

use std::fmt;

impl fmt::Display for FType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FType::uint => write!(f, "uint"),
            FType::Usize => write!(f, "usize"),
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
            FType::Variadic(t) => write!(f, "...{t}"),
            FType::Function(args, ret) => {
                write!(f, "func(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{arg}")?;
                }
                write!(f, ") -> {ret}")
            }
        }
    }
}

impl FType {
    pub fn variadic_parts(args: &[FType]) -> (usize, Option<&FType>) {
        match args.last() {
            Some(FType::Variadic(t)) => (args.len() - 1, Some(t)),
            _ => (args.len(), None),
        }
    }

    pub fn is_vararg_scalar(&self) -> bool {
        self.is_numerical() || matches!(self, FType::bool | FType::strconst | FType::Ptr | FType::StructPtr(_) | FType::Function(..))
    }

    pub fn c_promoted(&self) -> FType {
        match self {
            FType::single => FType::double,
            FType::bool | FType::ubyte | FType::ibyte | FType::ushort | FType::ishort => FType::i32,
            _ => self.clone(),
        }
    }

    pub fn abi_signature(args: &[FType], ret: &FType) -> (Vec<FType>, FType, bool) {
        let (fixed, tail) = Self::variadic_parts(args);
        let mut params = args[..fixed].to_vec();
        let mut result = ret.clone();
        if matches!(ret, FType::Struct(_)) {
            params.insert(0, FType::Ptr);
            result = FType::Ptr;
        }
        if let Some(el) = tail {
            if !matches!(el, FType::none) {
                params.extend([FType::Array(Box::new(el.clone()), 0), FType::uint]);
            }
        }
        (params, result, matches!(tail, Some(FType::none)))
    }

    pub fn is_compatible_with(&self, other: &FType) -> bool {
        match (self, other) {
            (_, FType::any) | (FType::any, _) => true,
            (FType::Array(a, n), FType::Array(b, m)) =>
                a.is_compatible_with(b) && (n == m || *n == 0 || *m == 0),
            _ => self == other,
        }
    }

    pub fn size(&self, tgt: Option<Target>) -> u64 {
        match self {
            FType::Ptr if tgt.is_some() => {
                let t = tgt.unwrap();
                t.ptrsize()
            }   
            other => mirtoqbe::QBEBackend::match_ft_qbf_t(
                other, true 
            ).size()
        }
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

    pub fn is_signed(&self) -> bool {
        match self {
            FType::ibyte | FType::ishort | FType::i32 | FType::int
                | FType::single | FType::double => true,
            _ => false,
        }
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
                match &fa.ftype {
                    FType::Variadic(el) => FType::Array(el.clone(), 0),
                    other => other.clone(),
                }
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

    pub fn set_module(&mut self, module: String) { self.module = module; }

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
                let rightdat = self.analyze_expr(&AstRoot::new(*val.clone(), self.line), logger);
                self.expect_type = FType::none;

                if Self::is_move_type(&rightdat.ftype) {
                    if let Some(var) = rightdat.var_name.as_ref() {
                        self.try_move(&mut logger.clone(), var, self.line);
                    }
                }

                if self.symb_table.get(&name).is_some() {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::Redeclaration(name.to_owned())),
                        self.line,
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
                            let visibility_name = si.generic_origin.as_deref().unwrap_or(&name);
                            let supermod = {
                                let mut spl: Vec<&str> = visibility_name.split("::").collect();
                                spl.pop();
                                spl.join("::")
                            };
                            if !si.public && !self.module.contains(&supermod) {
                                logger.send(LogMessage::new(
                                    LogLevel::Error(ErrKind::NotPubStruct(name.to_owned())),
                                    self.line,
                                    self.fname.clone()
                                ));                                
                            }
                        } else {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::UnknownStruct(name.to_owned())),
                                self.line,
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
                                self.line,
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
                                self.line,
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
                let leftd = self.analyze_expr(&AstRoot::new(*left.clone(), self.line), logger);
                let rightd = self.analyze_expr(&AstRoot::new(*right.clone(), self.line), logger);

                let is_shift_op =
                    (*op == BinaryOp::BitShiftLeft) || (*op == BinaryOp::BitShiftRight);

                if is_shift_op {
                    // For shift operations, right operand must be uint or pointer
                    let is_valid_shift_right_type =
                        matches!(rightd.ftype, FType::uint | FType::heapptr);

                    if !is_valid_shift_right_type {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::BitShiftRHSType(*op, rightd.ftype)),
                            self.line,
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
                            self.line,
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
                        self.line,
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
                let rdat = self.analyze_expr(&AstRoot::new(*expr.clone(), self.line), logger);
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
                        self.line,
                        self.fname.clone(),
                    ));
                }

                match *op {
                    UnaryOp::AddressOf => match rdat.ftype {
                        FType::Struct(s) => exprdat.ftype = FType::StructPtr(s),
                        other => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::NoStructAddress("Address Of".to_owned(), other)),
                                self.line,
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
                                self.line,
                                self.fname.clone(),
                            ));
                        }
                    },
                    _ => {} 
                }
            }
            AstNode::Variable(var) => {
                let paths = self.get_use_paths();
                if self.symb_table.get(var).is_some() {
                    exprdat.var_name = Some(var.clone());
                    self.chk_move(&mut logger.clone(), var, &mut exprdat, self.line);
                    return exprdat;
                }
                if let Some(_v) = self.struct_tab.get(var, &paths) {
                    exprdat.ftype = FType::Struct(var.to_owned());
                    return exprdat;
                }
    
                if let Some(funcs) = self.func_table.get_func(var, &paths) {
                    if funcs.len() != 1 || !funcs[0].name.get_generics().is_empty() {
                        self.signature_error(logger, "Taking an overloaded or generic function as a value is not supported");
                    } else {
                        let f = &funcs[0];
                        let owner = f.name.path_to_string().rsplit_once("::").map(|(m, _)| m.to_owned()).unwrap_or_default();
                        if !f.public && owner != self.module {
                            self.signature_error(logger, "Cannot take the address of a private function from another module");
                        }
                        exprdat.ftype = f.function_type();
                    }
                    return exprdat;
                }
                if let Some((owner, variant)) = var.rsplit_once("::") {
                    if self.struct_tab.get(owner, &paths).map(|s| s.is_enum() && s.fields.contains_key(variant)).unwrap_or(false) {
                        return self.analyze_expr(&AstRoot::new(AstNode::Call {
                            func_name: Box::new(AstNode::string_to_path(var)), args: vec![], idx: usize::MAX,
                        }, self.line), logger);
                    }
                }

                exprdat.var_name = Some(var.clone());
                self.chk_move(&mut logger.clone(), &var, &mut exprdat, self.line); 
            }
            AstNode::Reassignment { name, idx, newval } => {
                let val = self.analyze_expr(
                    &AstRoot::new(*name.clone(), self.line), 
                    &logger.clone()
                );
                let newval_data = self.analyze_expr(&newval, logger);
                match &newval_data.ftype {
                    ft if Self::is_move_type(ft) && newval_data.var_name.is_some() => {
                        self.try_move(
                            &mut logger.clone(),
                            &newval_data.var_name.unwrap(),
                            self.line
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
                        self.line,
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
                    self.permissive_error(self.line, logger.clone(), lerr, lwarn);
                }

                let then_data = self.analyze_expr(if_true, logger);
                if let Some(iff_root) = if_false {
                    let else_data = self.analyze_expr(iff_root, logger);
                    exprdat.has_returned = then_data.has_returned && else_data.has_returned;
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
                            self.line,
                            self.fname.clone()
                        ));
                    }
                    self.chk_cast(&var_ft, target_type, logger.clone());
                } else {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::UndeclaredVar(name.to_owned())),
                        self.line,
                        self.fname.clone()
                    ));
                }

                exprdat.ftype = target_type.clone();
            }
            AstNode::Intrinsic { intr, val } => {
                let rdat = self.analyze_expr(&AstRoot::new(*val.clone(), self.line), logger);
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
                                    self.line,
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
            AstNode::Match { value, arms } => {
                let value_dat = self.analyze_expr(value, logger);
                let mut result_type: Option<FType> = None;
                let mut covered = HashSet::new();
                let mut wildcard = false;
                let mut all_returned = !arms.is_empty();
                let paths = self.get_use_paths();
                let enum_info = value_dat.ftype.if_struct().and_then(|name| self.struct_tab.get(&name, &paths)).filter(|s| s.is_enum());
                for (pattern, body) in arms {
                    let mut binding = None;
                    if wildcard { self.signature_error(logger, "Unreachable pattern after wildcard"); }
                    match pattern {
                        MatchPattern::Wildcard => wildcard = true,
                        MatchPattern::Int(v) => {
                            if !matches!(value_dat.ftype, FType::int | FType::i32 | FType::ishort | FType::ibyte) {
                                self.signature_error(logger, "Signed integer pattern requires a signed integer value");
                            }
                            covered.insert(format!("int:{v}"));
                        }
                        MatchPattern::Uint(v) => {
                            if !matches!(value_dat.ftype, FType::uint | FType::u32 | FType::ushort | FType::ubyte) {
                                self.signature_error(logger, "Unsigned integer pattern requires an unsigned integer value");
                            }
                            covered.insert(format!("uint:{v}"));
                        }
                        MatchPattern::Bool(v) => {
                            if value_dat.ftype != FType::bool { self.signature_error(logger, "Boolean pattern requires a bool value"); }
                            covered.insert(v.to_string());
                        }
                        MatchPattern::Path(path) | MatchPattern::PathBinding(path, _) => {
                            let (owner, variant) = path.path_to_string().rsplit_once("::").map(|(a,b)| (a.to_owned(),b.to_owned())).unwrap_or_default();
                            let info = self.struct_tab.get(&owner, &paths);
                            match info.filter(|info| enum_info.as_ref().map(|e| &e.name) == Some(&info.name)) {
                                Some(info) if info.fields.contains_key(&variant) => {
                                    let field = &info.fields[&variant];
                                    covered.insert(variant);
                                    if let MatchPattern::PathBinding(_, name) = pattern {
                                        if field.ftype == FType::none { self.signature_error(logger, "Cannot bind a unit variant payload"); }
                                        else { binding = Some((name.clone(), field.ftype.clone())); }
                                    }
                                }
                                _ => self.signature_error(logger, "Pattern must name a variant of the matched enum"),
                            }
                        }
                    }
                    self.symb_table.enter_scope();
                    if let Some((name, ftype)) = binding { self.symb_table.newsymb(FSymbol::new(name, VarPosition::None, ftype)); }
                    let body_dat = self.analyze_expr(body, logger);
                    self.symb_table.exit_scope();
                    all_returned &= body_dat.has_returned;
                    if !body_dat.has_returned {
                        if let Some(expected) = &result_type {
                            if expected != &body_dat.ftype {
                                let _ = logger.send(LogMessage::new(LogLevel::Error(ErrKind::MismatchedTypes(expected.clone(), body_dat.ftype.clone())), self.line, self.fname.clone()));
                            }
                        } else { result_type = Some(body_dat.ftype); }
                    }
                }
                let exhaustive = wildcard || match &enum_info {
                    Some(info) => info.fields.keys().all(|name| covered.contains(name)),
                    None if value_dat.ftype == FType::bool => covered.contains("true") && covered.contains("false"),
                    _ => false,
                };
                if !exhaustive { self.signature_error(logger, "Non-exhaustive match: cover every variant or add `_ => ...`"); }
                exprdat.ftype = result_type.unwrap_or(FType::none);
                exprdat.has_returned = exhaustive && all_returned;
            }

            AstNode::CodeBlock { exprs } => {
                self.symb_table.enter_scope();
                for expr in exprs {
                    let ed = self.analyze_expr(expr, logger);
                    exprdat.has_returned = ed.has_returned;
                    exprdat.ftype = ed.ftype;
                    if ed.has_returned { break; }
                }
                self.symb_table.exit_scope();
            }
            AstNode::WhileLoop { cond, body } => {
                self.parsing_loop.push(self.parsing_loop.len());

                let cond_dat = self.analyze_expr(&cond, logger);
                if cond_dat.ftype != FType::bool {
                    self.permissive_error(
                        self.line,
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
                        self.line,
                        self.fname.clone()
                    ));
                }
            }
            AstNode::ContinueLoop => {
                if self.parsing_loop.len() == 0 {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::ContinueNotLoop), 
                        self.line,
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
                self.validate_variadic_args(args, false, logger);
                if name.path_to_string() == "main::main" && args.iter().any(|a| matches!(a.ftype, FType::Variadic(_))) {
                    self.signature_error(logger, "The program entry point cannot be variadic");
                }
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
                            self.line,
                            self.fname.clone()
                        ));
                    }
                } else {
                    self.declared_parse.insert(name.path_to_string(), self.line);
                }

                let generics = name.get_generics();
                let generic_names = name.get_generic_names();

                for arg in args {
                    match &arg.ftype {
                        ft if ft.if_struct().is_some() => {
                            let name = ft.if_struct().unwrap();
                            let paths = self.get_use_paths();
                            if let Some(si) = self.struct_tab.get(&name, &paths) {
                                let visibility_name = si.generic_origin.as_deref().unwrap_or(&name);
                                let supermod = {
                                    let mut spl: Vec<&str> = visibility_name.split("::").collect();
                                    spl.pop();
                                    spl.join("::")
                                };
                                if !si.public && !self.module.contains(&supermod) {
                                    logger.send(LogMessage::new(
                                        LogLevel::Error(ErrKind::NotPubStruct(name.to_owned())),
                                        self.line,
                                        self.fname.clone()
                                    ));                                
                                }
                            } else {
                                let last_seg = name.rsplit("::").next().unwrap();
                                if !(generic_names.iter().any(|g| g == last_seg)) {
                                    logger.send(LogMessage::new(
                                        LogLevel::Error(ErrKind::UnknownStruct(name.to_owned())),
                                        self.line,
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
                        self.line,
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
                self.validate_variadic_args(args, true, logger);
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
                            self.line,
                            self.fname.clone()
                        ));
                    }
                } else {
                    self.declared_parse.insert(name.path_to_string(), self.line);
                }

                self.symb_table.enter_scope();
                self.symb_table.push_funcargs(args.to_vec());

                self.symb_table.exit_scope();
                self.parsing_func = None;
            }
            AstNode::FunctionOverload { func, idx, public: _ } => {
                self.parsing_func = Some(("".to_owned(), *idx));
                self.analyze_expr(&AstRoot::new(*func.clone(), self.line), logger);
            }
            AstNode::CallValue { callee, args } => {
                let signature = self.analyze_expr(&AstRoot::new(*callee.clone(), self.line), logger).ftype;
                if let FType::Function(params, ret) = signature {
                    let (fixed, tail) = FType::variadic_parts(&params);
                    if args.len() < fixed || (tail.is_none() && args.len() != fixed) {
                        self.signature_error(logger, "Incorrect argument count in function pointer call");
                    }
                    for (i, arg) in args.iter().enumerate() {
                        let data = self.analyze_expr(arg, logger);
                        let expected = params.get(i).filter(|_| i < fixed).or(tail);
                        if let Some(expected) = expected {
                            if (matches!(expected, FType::none) && !data.ftype.is_vararg_scalar())
                                || (!matches!(expected, FType::none) && !data.ftype.is_compatible_with(expected)) {
                                self.signature_error(logger, "Incompatible argument in function pointer call");
                            }
                        }
                        if Self::is_move_type(&data.ftype) {
                            if let Some(var) = data.var_name { self.try_move(&mut logger.clone(), &var, self.line); }
                        }
                    }
                    exprdat.ftype = *ret;
                } else {
                    self.signature_error(logger, "Called value is not a function pointer");
                }
            }
            AstNode::Call {
                func_name,
                args,
                idx,
            } => {
                let f_name_s = func_name.path_to_string();
                let paths = self.get_use_paths();
                let local_name = f_name_s.strip_prefix(&format!("{}::", self.module)).unwrap_or(&f_name_s);
                if self.symb_table.get(local_name).is_some() {
                    return self.analyze_expr(&AstRoot::new(AstNode::CallValue {
                        callee: Box::new(AstNode::Variable(local_name.into())), args: args.clone(),
                    }, self.line), logger);
                }

                if let Some((enum_name, variant)) = f_name_s.rsplit_once("::") {
                    if let Some(info) = self.struct_tab.get(enum_name, &paths) {
                        if info.is_enum() {
                            if let Some(field) = info.fields.get(variant) {
                                if args.len() != if matches!(field.ftype, FType::none) { 0 } else { 1 } {
                                    logger.send(LogMessage::new(
                                        LogLevel::Error(ErrKind::FuncArgsTypeIncompat(f_name_s.clone())),
                                        self.line, self.fname.clone()));
                                    return exprdat;
                                }
                                if let Some(arg) = args.first() {
                                    let actual = self.analyze_expr(arg, logger);
                                    if actual.ftype != field.ftype {
                                        logger.send(LogMessage::new(
                                            LogLevel::Error(ErrKind::MismatchFieldsTypes(
                                                variant.to_owned(), field.ftype.clone(), actual.ftype)),
                                            self.line, self.fname.clone()));
                                        return exprdat;
                                    }
                                }
                                self.matched_overloads.insert(*idx, (None, FType::Struct(info.name.clone())));
                                exprdat.ftype = FType::Struct(info.name.clone());
                                return exprdat;
                            }
                        }
                    }
                }

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
                            self.line,
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
                    
                    let params = overload.args.iter().map(|a| a.ftype.clone()).collect::<Vec<_>>();
                    let (fixed, tail) = FType::variadic_parts(&params);
                    if args.len() < fixed || (tail.is_none() && args.len() != fixed) {
                        continue;
                    }

                    let generics: HashMap<String, GenericType> = overload.name
                        .get_generics()
                        .iter()
                        .map(|e| {(e.name.clone(), e.clone())})
                        .collect();
                    let mut substitutions: HashMap<String, FType> = HashMap::new();
                    let mut arg_vars: Vec<Option<String>> = Vec::with_capacity(args.len());

                    for (idx, arg) in args.iter().enumerate() {
                        let argdat = self.analyze_expr(arg, logger); 
                        arg_vars.push(argdat.var_name.clone());
                        if idx >= fixed {
                            let expected = tail.unwrap();
                            if matches!(expected, FType::none) {
                                flag_matches &= argdat.ftype.is_vararg_scalar();
                            } else {
                                flag_matches &= argdat.ftype.is_compatible_with(expected);
                            }
                            continue;
                        }

                        if let FType::Generic(name) = &overload.args[idx].ftype {
                            substitutions.insert(name.clone(), argdat.ftype.clone());
                            continue;
                        }
                        let mut generic_owner_matches = false;
                        if let (Some(expected_struct), Some(passed_struct)) =
                            (overload.args[idx].ftype.if_struct(), argdat.ftype.if_struct()) {
                            let expected_template = self.struct_tab.template_name(&expected_struct);
                            if let Some(info) = self.struct_tab.tab.get(&passed_struct) {
                                if info.generic_origin.as_deref() == Some(expected_template.as_str()) {
                                    generic_owner_matches = discriminant(&overload.args[idx].ftype) == discriminant(&argdat.ftype);
                                    let template = self.struct_tab.tab.get(&expected_template);
                                    if let Some(template) = template {
                                        let mut params: Vec<String> = template.generic_params.iter()
                                            .map(|g| g.name.clone()).collect();
                                        for (param, arg) in params.into_iter().zip(info.generic_args.iter()) {
                                            substitutions.insert(param, arg.clone());
                                        }
                                    }
                                }
                            }
                        }

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
                                                                     
                        if !generic_owner_matches && !argdat.ftype
                                .is_compatible_with(&overload.args[idx].ftype) {
                            flag_matches = false;
                            break;
                        }
                        let resolved_ret = substitute_ftype(&overload.ret_type, &substitutions);
                        if self.expect_type != FType::none && self.expect_type != resolved_ret
                        {
                            flag_matches = false;
                            break;
                        }
                    }
                    if flag_matches {
                        let ov_idx_op = Some(over_idx);
                       
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
                                self.line,
                                self.fname.clone()
                            ));
                            return exprdat;
                        } 
                        let resolved_ret = substitute_ftype(&overload.ret_type, &substitutions);
                        self.matched_overloads.insert(*idx, 
                            (ov_idx_op, resolved_ret.clone())
                        );
                        for (arg_idx, var) in arg_vars.iter().enumerate() {
                            if arg_idx >= fixed { continue; }
                            if let Some(var) = var {
                                let expected = &overload.args[arg_idx].ftype;
                                if Self::is_move_type(expected)
                                    || matches!(expected, FType::Generic(_))
                                        && self.symb_table.get(var)
                                            .map(|(_, sym)| Self::is_move_type(&sym.ftype))
                                            .unwrap_or(false) {
                                    self.try_move(&mut logger.clone(), var, self.line);
                                }
                            }
                        }
                        exprdat.ftype = resolved_ret;
                        return exprdat;
                    }
                }

                logger.send(LogMessage::new(
                    LogLevel::Error(ErrKind::FuncArgsTypeIncompat(func_name.path_to_string())),
                    self.line,
                    self.fname.clone()
                ));
            }
            AstNode::ReturnVal { val } => {
                let retval = self.analyze_expr(&*val, logger);
                if Self::is_move_type(&retval.ftype) {
                    if let Some(var) = retval.var_name.as_ref() {
                        self.try_move(&mut logger.clone(), var, self.line);
                    }
                }
                
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
                                self.line,
                                self.fname.clone()
                            ));
                        }
                        match retval.ftype {
                            FType::StructPtr(_) => {
                                logger.send(LogMessage::new(
                                    LogLevel::Warning(WarnKind::RawPtrRet(retval.ftype)),
                                    self.line,
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
                        self.line,
                        self.fname.clone()
                    ));
                };
            }
            AstNode::ExprCast { expr, target_type } => {
                let expr = self.analyze_expr(&AstRoot::new(*expr.clone(), self.line), logger);
                self.chk_cast(&expr.ftype, target_type, logger.clone());
                if &expr.ftype == target_type {
                    logger.send(LogMessage::new(
                        LogLevel::Warning(WarnKind::ConvSame(expr.ftype)), 
                        self.line,
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

                    let ndat = self.analyze_expr(&AstRoot::new(node.clone(), self.line), logger);
                    if ndat.ftype != *ft {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::IncompatArrType(ft.clone(),
                                                    ndat.ftype, idx)),
                            self.line,
                            self.fname.clone()
                        ));
                    }
                    if ndat.var_name.is_some() {
                        self.try_move(
                            &mut logger.clone(), 
                            ndat.var_name.as_ref().unwrap(),
                            self.line
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
                let arr_nm = match &**arr {
                    AstNode::Variable(nm) => nm.clone(),
                    other => "".into()
                };

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
                            format!("{}", arr_nm), 
                            idx_exprdat.ftype
                        )),
                        self.line,
                        self.fname.clone()
                    ));
                }

                let el_type_u = match elem_type {
                    Some(v) => v,
                    None => {
                        logger.send(LogMessage::new(
                            LogLevel::Error(ErrKind::Internal("Can't match type".to_owned())),
                            self.line,
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
                                self.line, 
                                self.fname.clone()
                        ));
                        return exprdat;
                    }
                };
                if struct_data.attrs.contains(&Attr::Heap) {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::HeapOnlyStack(exprdat.ftype.clone())),
                        self.line,
                        self.fname.clone()
                    ));
                }

                let valid_field_count = if struct_data.is_union() { field_vals.len() == 1 } else {
                    struct_data.fields.len() == field_vals.len()
                };
                if !valid_field_count {
                    logger.send(LogMessage::new(
                        LogLevel::Error(ErrKind::MismatchFieldsCount(
                            struct_data.fields.len(),
                            field_vals.len()
                        )), 
                        self.line, 
                        self.fname.clone()
                    ));
                    return exprdat;
                }

                for (field_name, field_val) in field_vals {
                    let expected = struct_data.fields.get(field_name)
                        .unwrap();

                    let field_ed = self.analyze_expr(
                        &AstRoot::new(*field_val.clone(), self.line), 
                        &logger.clone()
                    );

                    match &expected.ftype {
                        FType::Array(el, ct) if (expected.ftype == field_ed.ftype)
                            && (*ct != 0) => {
                            if let Some(vn) = field_ed.var_name {
                                self.try_move(
                                    &mut logger.clone(),
                                    &vn,
                                    self.line
                                );
                            };
                        }
                        ft if Self::is_move_type(ft) => {
                            if let Some(vn) = field_ed.var_name {
                                self.try_move(
                                    &mut logger.clone(),
                                    &vn,
                                    self.line
                                );
                            };
                        }
                        other if *other != field_ed.ftype => {
                            logger.send(LogMessage::new(
                                LogLevel::Error(ErrKind::MismatchFieldsTypes(
                                    field_name.clone(), expected.ftype.clone(), field_ed.ftype
                                )), 
                                self.line, 
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
                            self.line,
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
                            self.line,
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
                            self.line,
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
                let old_generic = self.in_generic.clone();
                self.in_generic = name.get_generics().into_iter()
                    .map(|g| (g.name.clone(), g))
                    .collect();
                for f in fields {
                    match f {
                        AstNode::StructField { name, ftype, public } => {
                            if let Some(sn) = ftype.if_struct() {
                                let paths = self.get_use_paths();
                                let unresolved_generic = self.in_generic.keys()
                                    .any(|generic| sn.ends_with(&format!("::{}", generic)));
                                if self.struct_tab.get(&sn, &paths).is_none() && !unresolved_generic {
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
                self.in_generic = old_generic;
            }
            AstNode::StructImpl { name, body, Trait } => {
                let old_mod = self.module.clone();
                let old_generic = self.in_generic.clone();
                self.module = name.path_to_string();
                self.in_generic = name.get_generics().into_iter()
                    .map(|g| (g.name.clone(), g))
                    .collect();
                
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
                self.in_generic = old_generic;

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

                let paths = self.get_use_paths();
                if self.struct_tab.get(&struct_name, &paths).and_then(|s| s.fields.get(&name.path_to_string()).cloned()).is_some() {
                    return self.analyze_expr(&AstRoot::new(AstNode::CallValue {
                        callee: Box::new(AstNode::StructFieldAddr { val: Box::new(first_arg.clone()), field_name: name.path_to_string() }),
                        args: args[1..].to_vec(),
                    }, self.line), logger);
                }

                let func_name = format!("{}::{}",
                    self.struct_tab.template_name(&struct_name),
                    name.path_to_string());

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
        let numeric = |ft: &FType| matches!(ft,
            FType::int | FType::uint | FType::i32 | FType::u32 |
            FType::ubyte | FType::ibyte | FType::ushort | FType::ishort |
            FType::single | FType::double);
        let enum_to_uint = match from {
            FType::Struct(name) => {
                let paths = self.get_use_paths();
                self.struct_tab.get(name, &paths).map(|info| info.is_enum()).unwrap_or(false)
                    && matches!(to, FType::uint | FType::u32 | FType::ushort | FType::ubyte)
            }
            _ => false,
        };
        let allowed = from == to || (numeric(from) && numeric(to)) || enum_to_uint || matches!(
            (from, to),
            (FType::Ptr, FType::StructPtr(_)) |
            (FType::Ptr, FType::Struct(_)) |
            (FType::Ptr, FType::StructHeapPtr(_)) |
            (FType::StructHeapPtr(_), FType::StructPtr(_))
        );
        if !allowed {
            logger.send(LogMessage::new(
                LogLevel::Error(ErrKind::IllegalCast(from.clone(), to.clone())),
                self.line, self.fname.clone()));
        }
    }

    fn signature_error(&self, logger: &Sender<LogMessage>, message: &str) {
        let _ = logger.send(LogMessage::new(
            LogLevel::Error(ErrKind::InvalidSignature(message.to_owned())), self.line, self.fname.clone()));
    }

    fn validate_variadic_args(&self, args: &[FuncArg], external: bool, logger: &Sender<LogMessage>) {
        for (i, arg) in args.iter().enumerate() {
            if let FType::Variadic(el) = &arg.ftype {
                if i + 1 != args.len() {
                    self.signature_error(logger, "A variadic parameter must be last");
                }
                if external != matches!(**el, FType::none) {
                    self.signature_error(logger, "Use `...` for externs and `name: ...T` for Fency functions");
                }
                if external && i == 0 {
                    self.signature_error(logger, "An external variadic function needs at least one fixed parameter");
                }
                if !external && !el.is_vararg_scalar() {
                    self.signature_error(logger, "Typed variadic tails currently require a copyable scalar or function pointer element type");
                }
            }
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

        // Ownership is intentionally shallow: owning structs and heap pointers
        // become unusable after transfer; raw pointers remain copyable.
        match &var_ref.ftype {
            FType::Struct(_) | FType::StructHeapPtr(_) => {
               var_ref.moved = Some(line);
            }
            FType::Array(el, _) if matches!(**el, FType::Struct(_)) => {
                var_ref.moved = Some(line);
            }
            other => {}
        }
    }

    fn is_move_type(ft: &FType) -> bool {
        matches!(ft, FType::Struct(_) | FType::StructHeapPtr(_))
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct StructInfo {
    pub name: String,
    pub fields: IndexMap<String, StructField>,
    pub size: usize, 
    pub max_alignment: usize,
    pub public: bool,
    pub attrs: Vec<Attr>,
    pub generic_params: Vec<GenericType>,
    pub generic_origin: Option<String>,
    pub generic_args: Vec<FType>,
}

impl StructInfo {
    pub fn is_union(&self) -> bool {
        self.attrs.contains(&Attr::Custom("union".into()))
    }

    pub fn is_enum(&self) -> bool {
        self.attrs.contains(&Attr::Custom("enum".into()))
    }

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
                    generic_params: name.get_generic_names().iter().map(|param| name.get_generics().into_iter().find(|g| &g.name == param).unwrap()).collect(),
                    generic_origin: None,
                    generic_args: Vec::new(),
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
            FType::none => 1,
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub offset: usize,
    pub ftype: FType,
    pub public: bool,
}

pub fn substitute_ftype(ft: &FType, substitutions: &HashMap<String, FType>) -> FType {
    match ft {
        FType::Generic(name) => substitutions.get(name).cloned()
            .unwrap_or_else(|| ft.clone()),
        FType::Struct(name) => substitute_named_struct(FType::Struct, name, substitutions),
        FType::StructPtr(name) => substitute_named_struct(FType::StructPtr, name, substitutions),
        FType::StructHeapPtr(name) => substitute_named_struct(FType::StructHeapPtr, name, substitutions),
        FType::Array(el, count) => FType::Array(
            Box::new(substitute_ftype(el, substitutions)), *count
        ),
        FType::Variadic(el) => FType::Variadic(Box::new(substitute_ftype(el, substitutions))),
        FType::Function(args, ret) => FType::Function(args.iter().map(|t| substitute_ftype(t, substitutions)).collect(), Box::new(substitute_ftype(ret, substitutions))),
        other => other.clone(),
    }
}

fn substitute_named_struct(
    ctor: fn(String) -> FType,
    name: &str,
    substitutions: &HashMap<String, FType>,
) -> FType {
    if let Some(ft) = substitutions.get(name) {
        return match ctor(String::new()) {
            FType::Struct(_) => ft.clone(),
            FType::StructPtr(_) => match ft {
                FType::Struct(name) | FType::StructPtr(name) | FType::StructHeapPtr(name)
                    => FType::StructPtr(name.clone()),
                _ => ft.clone(),
            },
            FType::StructHeapPtr(_) => match ft {
                FType::Struct(name) | FType::StructPtr(name) | FType::StructHeapPtr(name)
                    => FType::StructHeapPtr(name.clone()),
                _ => ft.clone(),
            },
            _ => ft.clone(),
        };
    }
    for (param, arg) in substitutions {
        if name == param {
            return match ctor(String::new()) {
                FType::Struct(_) => arg.clone(),
                FType::StructPtr(_) => match arg {
                    FType::Struct(name) | FType::StructPtr(name) | FType::StructHeapPtr(name)
                        => FType::StructPtr(name.clone()),
                    _ => FType::Ptr,
                },
                FType::StructHeapPtr(_) => match arg {
                    FType::Struct(name) | FType::StructPtr(name) | FType::StructHeapPtr(name)
                        => FType::StructHeapPtr(name.clone()),
                    _ => FType::Ptr,
                },
                _ => arg.clone(),
            };
        }
        let suffix = format!("::{}", param);
        if let Some(base) = name.strip_suffix(&suffix) {
            return match ctor(String::new()) {
                FType::Struct(_) => ctor(fparse::generic_instance_name(base, &[arg.clone()])),
                FType::StructPtr(_) | FType::StructHeapPtr(_) => match arg {
                    FType::Struct(name) | FType::StructPtr(name) | FType::StructHeapPtr(name)
                        => ctor(name.clone()),
                    _ => FType::Ptr,
                },
                _ => ctor(name.to_owned()),
            };
        }
    }
    ctor(name.to_owned())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LayoutMark {
    Visiting,
    Done,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
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

    pub fn template_name(&self, name: &str) -> String {
        self.tab.get(name)
            .and_then(|info| info.generic_origin.clone())
            .unwrap_or_else(|| name.to_owned())
    }

    pub fn instantiate_many(&mut self, uses: &[(String, Vec<FType>)]) {
        let mut pending: Vec<(String, Vec<FType>)> = uses.to_vec();
        let mut cursor = 0;
        while cursor < pending.len() {
            let (base, args) = pending[cursor].clone();
            cursor += 1;

            if args.iter().any(|arg| matches!(arg, FType::Generic(_))) {
                continue;
            }
            let template = match self.tab.get(&base).cloned() {
                Some(info) if !info.generic_params.is_empty() => info,
                _ => continue,
            };
            if template.generic_params.len() != args.len() {
                continue;
            }

            let name = fparse::generic_instance_name(&base, &args);
            if self.tab.contains_key(&name) {
                continue;
            }

            let mut substitutions = HashMap::new();
            let mut params: Vec<String> = template.generic_params.iter()
                .map(|g| g.name.clone())
                .collect();
            for (param, arg) in params.iter().zip(args.iter()) {
                substitutions.insert(param.clone(), arg.clone());
            }

            let mut concrete = template.clone();
            concrete.name = name.clone();
            concrete.generic_params.clear();
            concrete.generic_origin = Some(base.clone());
            concrete.generic_args = args.clone();
            for field in concrete.fields.values_mut() {
                field.ftype = substitute_ftype(&field.ftype, &substitutions);
            }
            let nested: Vec<(String, Vec<FType>)> = concrete.fields.values()
                .filter_map(|field| generic_use_from_ftype(&field.ftype, self))
                .collect();
            self.tab.insert(name, concrete);
            pending.extend(nested);
        }
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
        let names: Vec<String> = self.tab.iter()
            .filter(|(_, info)| info.generic_params.is_empty())
            .map(|(name, _)| name.clone())
            .collect();
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

        let is_union = self.tab.get(name).map(|i| i.is_union()).unwrap_or(false);
        let is_enum = self.tab.get(name).map(|i| i.is_enum()).unwrap_or(false);
        let mut offset = if is_enum { 8 } else { 0 };
        let mut max_align = 1usize;
        let mut max_union_size = 0usize;
        let mut computed_offsets: Vec<(String, usize)> = Vec::with_capacity(fields_snapshot.len());

        for (field_name, ftype) in fields_snapshot {
            let (field_size, field_align) = self.type_layout(&ftype, marks)?;

            max_align = max_align.max(field_align);
            if is_union {
                computed_offsets.push((field_name, 0));
                max_union_size = max_union_size.max(field_size);
            } else if is_enum {
                let payload_offset = Self::align_up(8, field_align);
                computed_offsets.push((field_name, payload_offset));
                offset = offset.max(payload_offset + field_size);
            } else {
                offset = Self::align_up(offset, field_align);
                computed_offsets.push((field_name, offset));
                offset += field_size;
            }
        }

        if is_union { offset = max_union_size; }
        if is_enum {
            max_align = max_align.max(8);
            offset = Self::align_up(offset, max_align);
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
            | FType::StructPtr(_) | FType::StructHeapPtr(_) | FType::Ptr | FType::Function(..) => Ok((8, 8)),

            FType::i32 | FType::u32 | FType::single => Ok((4, 4)),
            FType::bool | FType::ubyte | FType::ibyte => Ok((1, 1)),
            FType::ushort | FType::ishort => Ok((2, 2)),

            FType::Array(el, ct) => {
                let (elem_size, elem_align) = self.type_layout(el, marks)?;
                let (arr_size, arr_align) = match ct {
                    0 => self.type_layout(&FType::uint, marks)?, // ptr 
                    other => (elem_size * *ct, elem_align),
                };
                Ok((arr_size, arr_align))
            }

            FType::Struct(sn) => {
                self.layout_struct(&sn, marks)
            }

            FType::none => Ok((0, 1)),
            FType::Generic(_) => Err("generic field reached concrete layout".to_owned()),
            other => Err(format!("layout not implemented for {:?}", other)),
        }
    }

    fn align_up(offset: usize, align: usize) -> usize {
        (offset + align - 1) & !(align - 1)
    }
}

fn generic_use_from_ftype(ft: &FType, table: &StructTable) -> Option<(String, Vec<FType>)> {
    let name = ft.if_struct()?;
    for (template_name, template) in &table.tab {
        if template.generic_params.len() != 1 {
            continue;
        }
        let prefix = format!("{}::", template_name);
        if let Some(raw_arg) = name.strip_prefix(&prefix) {
            if let Some(arg) = type_from_key(raw_arg) {
                return Some((template_name.clone(), vec![arg]));
            }
        }
    }
    None
}

fn type_from_key(raw: &str) -> Option<FType> {
    match raw {
        "uint" => Some(FType::uint),
        "int" => Some(FType::int),
        "double" => Some(FType::double),
        "bool" => Some(FType::bool),
        "single" => Some(FType::single),
        "u32" => Some(FType::u32),
        "i32" => Some(FType::i32),
        "ushort" => Some(FType::ushort),
        "ishort" => Some(FType::ishort),
        "ubyte" => Some(FType::ubyte),
        "ibyte" => Some(FType::ibyte),
        "ptr" => Some(FType::Ptr),
        raw if raw.starts_with("s_") => Some(FType::Struct(raw[2..].to_owned())),
        raw if raw.starts_with("ptr_") => Some(FType::StructPtr(raw[4..].to_owned())),
        raw if raw.starts_with("h_") => Some(FType::StructHeapPtr(raw[2..].to_owned())),
        _ => None,
    }
}

pub struct SemanResult {
    fname: String,
    ast: Arc<AstRoot>,
    matched_overloads: Vec<OverloadTable>,
    has_error: bool,
}
