use crate::seman::seman::FType;

// Fencyc Medium IR 

pub trait MIRTranslator {
    type Output;

    fn translate_module(&mut self, module: &FModule) -> Self::Output;
    fn translate_function(&mut self, func: &FFunction);
    fn translate_block(&mut self, block: &FBlock);
    fn translate_instr(&mut self, instr: &FInstr);
    fn translate_term(&mut self, term: &FTerm);
}

#[derive(Debug, Clone)]
pub struct FModule {
    pub funcs: Vec<FFunction>,
    pub datadefs: Vec<FDataDef>,
    pub typedefs: Vec<FTypeDef>
}

impl FModule {
    pub fn new() -> FModule {
        FModule { 
            funcs: Vec::new(),
            datadefs: Vec::new(),
            typedefs: Vec::new()
        }
    }

    pub fn add_func(&mut self, func: FFunction) {
        self.funcs.push(func);
    }

    pub fn add_datadef(&mut self, def: FDataDef) {
        self.datadefs.push(def);
    }

    pub fn add_typedef(&mut self, def: FTypeDef) {
        self.typedefs.push(def);
    }
}

impl std::fmt::Display for FModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for typedef in self.typedefs.iter() {
            write!(f, "{}", typedef)?;
        }
        for func in self.funcs.iter() {
            write!(f, "{}", func)?;
        }
        for dat in self.datadefs.iter() {
            write!(f, "{}", dat)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct FFunction {
    pub name: String,
    pub public: bool,
    pub params: Vec<(FValue, FType)>,
    pub ret_ft: FType,
    pub blocks: Vec<FBlock>,
    cur_blk: usize,
}

impl FFunction {
    pub fn new(name: String, public: bool, params: Vec<(FValue, FType)>, 
        ret_ft: FType) 
        -> FFunction {
        FFunction { 
            name, 
            public, 
            params, 
            ret_ft, 
            blocks: Vec::new(), 
            cur_blk: 0
        }
    }

    /// Push block and return its id   
    pub fn add_blk(&mut self, blk: FBlock) -> usize {
        self.blocks.push(blk);
        self.blocks.len()
    }

    /// Set current block id
    pub fn set_cur_blkid(&mut self, new_id: usize) {
        self.cur_blk = new_id;
    }

    pub fn add_instr(&mut self, instr: FInstr) {
        self.blocks.get_mut(self.cur_blk)
            .expect(&format!("Expected block in func {}", self.name))
            .add_instr(instr);
    }

    pub fn assign_instr(&mut self, lhs: FValue, ft: FType, rhs: FInstr) {
        self.blocks.get_mut(self.cur_blk)
            .expect(&format!("Expected block in func {}", self.name))
            .assign_instr(lhs, ft, rhs);
    }

    pub fn add_term(&mut self, term: FTerm) {
        self.blocks.get_mut(self.cur_blk)
            .expect(&format!("Expected block in func {}", self.name))
            .set_term(term);
    }
}

fn pub_as_str(public: bool) -> String {
    match public {
        true => "pub ".into(),
        false => "".into()
    }
}

impl std::fmt::Display for FFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pub_sign = pub_as_str(self.public); 
        write!(f, "{}func {}(", pub_sign, self.name)?;
        for (i, p) in self.params.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", p.0, p.1)?;
        }
        write!(f, ") -> {}\n", self.ret_ft)?;
        for b in self.blocks.iter() {
            write!(f, "{}", b)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum FTerm {
    Return(Option<FValue>),
    Jump(String),
    Branch {
       cond: FValue,
       then_bl: String,
       else_bl: String
    },
    none, // only for inner use 
}

impl std::fmt::Display for FTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FTerm::Return(ofv) => match ofv {
                Some(fv) => writeln!(f, "ret {}", fv),
                None => writeln!(f, "ret")
            }
            FTerm::Jump(lbl) => writeln!(f, "jmp {}", lbl),
            FTerm::Branch { cond, then_bl, else_bl } => 
                writeln!(f, "br {} then {} else {}", cond, then_bl, else_bl),
            FTerm::none => writeln!(f, "(none term; bug or incomplete block)"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FBlock {
    pub name: String,
    pub instrs: Vec<FInstr>,
    pub term: FTerm,
}

impl FBlock {
    pub fn new(name: String) -> FBlock {
        FBlock { 
            name, 
            instrs: Vec::new(), 
            term: FTerm::none,
        }
    }

    pub fn add_instr(&mut self, instr: FInstr) {
        self.instrs.push(instr);
    }

    pub fn assign_instr(&mut self, lhs: FValue, ft: FType, rhs: FInstr) {
        self.instrs.push(FInstr::Assign(lhs, ft, Box::new(rhs)));
    }

    pub fn set_term(&mut self, term: FTerm) {
        self.term = term;
    }
}

impl std::fmt::Display for FBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}:\n", self.name)?;
        for i in self.instrs.iter() {
            writeln!(f, "\t{}", i)?;
        }
        write!(f, "\t{}\n", self.term)
    }
}

#[derive(Debug, Clone)]
pub enum FValue {
    VarTmp(String, FType), // temporary variable
    VarGlb(String, FType), // global variable 

    UConst(u64),
    IConst(i64),

    SingleConst(f32), // single precision float 
    DoubleConst(f64), // double precision float 
}

impl std::fmt::Display for FValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FValue::VarTmp(nm, ft) => write!(f, "%{nm}"),
            FValue::VarGlb(nm, ft) => write!(f, "${nm}"),

            FValue::UConst(v) => write!(f, "{v}"),
            FValue::IConst(v) => write!(f, "{v}"),
            FValue::SingleConst(v) => write!(f, "f_s{v}"),
            FValue::DoubleConst(v) => write!(f, "f_d{v}"),

            other => todo!("{:?}", other)
        }
    }
}


#[derive(Debug, Clone)]
pub enum FInstr {
    Assign(FValue, FType, Box<FInstr>), // name, type, val
    Copy(FType, FValue), // as ft, val

    BinaryOp(IRBinOp, FValue, FValue), 
    Neg(FValue), // arithmetical negation

    Call(String, Vec<(FValue, FType)>), // name, args

    Load(FValue, FType), // src, ft
    Store(FValue, FValue, FType), // dst, src, ft  
    GetAddr(FValue, FValue), // loads addr. args: base, offset 

    Cast(FValue, FType, FType), // val, from, to
}

// for debug 
impl std::fmt::Display for FInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FInstr::Assign(nm, ft, val) => write!(f, "{nm}: {ft} = {val}"),
            FInstr::Copy(ft, fv) => write!(f, "copy {ft} {fv}"),

            FInstr::BinaryOp(bop, v1, v2) => write!(f, "{v1} {bop} {v2}"),
            FInstr::Neg(v1) => write!(f, "-{v1}"),

            FInstr::Call(nm, args) => {
                write!(f, "call ${}(", nm)?;
                for (idx, (fv, ft)) in args.iter().enumerate() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} {}", ft, fv)?;
                }
                write!(f, ")")
            }

            FInstr::Load(src, ft) => write!(f, "load {ft} {src}"),
            FInstr::Store(dst, src, ft) => write!(f, "store {dst} {ft} {src}"),

            FInstr::GetAddr(base, ofs) => write!(f, "compaddr {base} + {ofs}"),

            FInstr::Cast(fv, ft_src, ft_dst) => write!(f, "cast {ft_src} {fv} into {ft_dst}"),
        }    
    }
}

#[derive(Debug, Clone)]
pub enum IRBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,

    And,
    Or,
    Xor,
}

impl std::fmt::Display for IRBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IRBinOp::Add => write!(f, "+"),
            IRBinOp::Sub => write!(f, "-"),
            IRBinOp::Mul => write!(f, "*"),
            IRBinOp::Div => write!(f, "/"),
            IRBinOp::Rem => write!(f, "%"),

            IRBinOp::And => write!(f, "&"),
            IRBinOp::Or  => write!(f, "|"),
            IRBinOp::Xor => write!(f, "^"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FDataDef {
    pub name: String,
    pub public: bool,
    pub align: Option<u64>,
    pub items: Vec<(FType, FDataItem)>,
}

impl FDataDef {
    pub fn new(nm: String, public: bool, align: Option<u64>,
        items: Vec<(FType, FDataItem)>) 
        -> FDataDef {
        FDataDef { 
            name: nm, 
            public, 
            align, 
            items 
        }
    }
}

fn align_as_str(align: Option<u64>) -> String {
    match align {
        Some(v) => format!("align{} ", v),
        None => "".to_owned()
    }
}

impl std::fmt::Display for FDataDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alignstr = align_as_str(self.align);

        write!(f, "{}data ${} {}= {{ ", 
            pub_as_str(self.public),
            self.name,
            alignstr
        )?;
        for (idx, entry) in self.items.iter().enumerate() {
            if idx != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} {}", entry.0, entry.1)?;
        }
        writeln!(f, " }}")
    }
}

#[derive(Debug, Clone)]
pub enum FDataItem {
    Str(String),
    Zeroes(usize), // count 
}

impl std::fmt::Display for FDataItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FDataItem::Str(s) => write!(f, "\"{s}\""),
            FDataItem::Zeroes(c) => write!(f, "z({c})"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FTypeDef {
    pub name: String, 
    pub align: Option<u64>,
    pub items: Vec<(FType, usize)>, // type, count 
}

impl FTypeDef {
    pub fn new(name: String, align: Option<u64>, items: Vec<(FType, usize)>)
        -> Self {
        FTypeDef { name, align, items }
    }
}

impl std::fmt::Display for FTypeDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alignstr = align_as_str(self.align);

        write!(f, "type ${} {}= {{ ", 
            self.name,
            alignstr
        )?;
        for (idx, entry) in self.items.iter().enumerate() {
            if idx != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} {}", entry.0, entry.1)?;
        }
        writeln!(f, " }}")
    }
}
