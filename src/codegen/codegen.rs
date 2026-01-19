use std::{collections::HashMap, fmt::format, rc::Rc};

use crate::{
    fcparse::fcparse::{self as fparse, AstRoot, CmpOp},
    lexer::lexer::Intrinsic,
    seman::seman::{self as sem, idx_to_ftype, FSymbol, FType, SemAn, SymbolTable, VarPosition},
}; // AstNode;
use fparse::AstNode;
use qbe::{Block, DataDef, DataItem, Function, Instr, Linkage, Module, Type, Value};

#[derive(Debug, Clone)]
pub enum ValDat {
    Symbol(FSymbTabData),
    ImmVal(Numerical), // immediate value
    None,
}

#[derive(Debug, Clone, Copy)]
pub enum Numerical {
    uint(u64),
    int(i64),
    float(f64),
    heapptr(u64),
    boolean(bool),
    None,
}

#[derive(Debug)]
pub struct CodeGen {
    ast: Vec<AstRoot>,
    cur_ast: usize,
    pub sbuf: String,
    pub module: Module,
    pub fbuild: FuncBuilder,
    pub symb_table: SymbolTable,
    should_push: bool,
    labels: HashMap<String, usize>, // usize for sbuf idx
    loop_exits: Vec<String>,
    loop_conts: Vec<String>,
    stackidxs: Vec<usize>, // saving last stack idx before function
    overload_ctr: usize,
    matched_overloads: HashMap<usize, usize>, // call idx -> overload idx
    arrays: HashMap<String, ArrayData>,
}

impl CodeGen {
    pub fn new(ast: Vec<AstRoot>, mo: HashMap<usize, usize>) -> CodeGen {
        CodeGen {
            ast: ast,
            cur_ast: 0,
            sbuf: String::new(),
            module: Module::new(),
            fbuild: FuncBuilder::new(),
            should_push: true,
            symb_table: SymbolTable::new(),
            labels: HashMap::new(),
            loop_exits: Vec::new(),
            loop_conts: Vec::new(),
            stackidxs: Vec::new(),
            overload_ctr: 0,
            matched_overloads: mo,
            arrays: HashMap::new(),
        }
    }

    pub fn gen_everything(&mut self) {
        self.gen_stddat();
        self.gen_prologue();
       
        while let Some(r) = self.ast.get(self.cur_ast) {
            let gdat = self.gen_expr(r.clone().node);
            self.cur_ast += 1;
        }
        
    }

    pub fn write_file(&mut self, fname: &str) -> Result<(), std::io::Error> {
        if let Some(parent) = std::path::Path::new(fname).parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(fname, &format!("{}", self.module))?;

        Ok(())
    }

    fn gen_prologue(&mut self) {
        let mut mainf = Function::new(
            Linkage::public(), 
            "main", 
            Vec::new(), 
            Some(Type::Word)
        );

        mainf.add_block("start");
        mainf.add_instr(
            Instr::Call("main_0".into(), Vec::new(), None)
        );
        mainf.add_instr(Instr::Ret(Some(Value::Const(0))));

        self.module.add_function(mainf);
    }

    fn gen_expr(&mut self, node: AstNode) -> GenData {
        let mut res = GenData::new();
        match node {
            AstNode::Function { name, args, ret_type, body } => {
                // TODO: pub 
                let mut args_qbe = Vec::new();
                for arg in args {
                    args_qbe.push((
                        Self::match_ft_qbf(arg.ftype),
                        Value::Temporary(arg.name.into())
                    ));
                }

                let ret_t_qbe = match ret_type {
                    FType::none | FType::nil => None,
                    other => Some(Self::match_ft_qbf(other))
                };


                let mut func = Function::new(
                    Linkage::private(), 
                    format!("{}_0", name),  // TODO: spec overloads
                    args_qbe, 
                    ret_t_qbe
                );
                func.add_block("start");
                self.fbuild.func = Some(func);
                self.fbuild.ready = false;
                self.should_push = false;
                {
                    let body_instrs = {
                        let instrs = {
                            let bgd = self.gen_expr(*body).clone();
                            bgd.instrs.clone()
                        };
                        instrs
                    };

                    for instr in body_instrs {
                        self.fbuild.add_instr(instr);
                    }
                }

                self.fbuild.add_instr(Instr::Ret(None));
                self.should_push = true;
                self.fbuild.ready = true;
            }
            AstNode::ReturnVal { val } => {
                //todo!();
            }
            AstNode::CodeBlock { exprs } => {
                for expr in exprs {
                    let gend = self.gen_expr(expr.node);
                    res.instrs.extend(gend.instrs);
                }
            }
            AstNode::Assignment { name, val, ft } => {
                let rdat = self.gen_expr(*val);

                let count = rdat.instrs.len().saturating_sub(1);
                for i in rdat.instrs.iter().take(count) {
                    self.fbuild.add_instr(i.clone());
                }
                let last_instr = rdat.instrs.last().unwrap_or_else(|| {
                    panic!("Internal error: can't get last instr of \
                        assignment")
                });

                self.fbuild.assign_instr(
                    Value::Temporary(name), 
                    Self::match_ft_qbf(ft), 
                    last_instr.clone()
                );
            }
            AstNode::Uint(uv) => {
                let val = Value::Const(uv); 
                res.instrs.push(
                    Instr::Load(Type::Long, val.clone())
                );
                res.val = Some(val);
                res.qtype = Some(Type::Long);
                res.ftype = FType::uint;
            }
            AstNode::Int(iv) => {
                let val = Value::Const(iv as u64); 
                res.instrs.push(
                    Instr::Load(Type::Long, val.clone())
                );
                res.val = Some(val);
                res.qtype = Some(Type::Long);
                res.ftype = FType::int;
            }
            AstNode::Float(fv) => {
                let val = Value::Const(fv.to_bits()); 
                res.instrs.push(
                    Instr::Load(Type::Long, val.clone())
                );
                res.val = Some(val);
                res.qtype = Some(Type::Double);
                res.ftype = FType::float; 
            }
            AstNode::BinaryOp { op, left, right } => {
                let leftd = self.gen_expr(*left);
                let rightd = self.gen_expr(*right);

                match op {
                    fparse::BinaryOp::Add => {
                        res.instrs.push(
                            Instr::Add(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            )
                        )
                    }
                    other => todo!("{:?}", other)
                }
            }
            AstNode::Intrinsic { intr, val } => {
                let gend = self.gen_expr(*val);
                
                let mut ind = self.gen_intrinsic(intr, gend);
                for instr in ind.instrs.drain(..) {
                    res.instrs.push(instr);
                }
            }
            other => {
                panic!("can't generate yet for {:?}", other);
            }
        }
        if let Some(f) = self.fbuild.pop_func() {
            self.module.add_function(f);
        };
        if self.should_push {
            for i in res.instrs.drain(..) {
                self.fbuild.add_instr(i);
            }
        }
        return res;
    }

    /// loads variable in place and returns register idx
    fn load_variable(&mut self, name: String, gend: &mut GenData) -> usize {
        return 0; 
    }

    /// This function will currently just return 8. In future, could be extended
    pub fn match_ftype_size(ft: FType) -> usize {
        match ft {
            _ => 8,
        }
    }

    pub fn match_jmp_op(cmp_op: CmpOp, label_name: &str) -> String {
        match cmp_op {
            CmpOp::Eq => format!("jz @{}\n", label_name),
            CmpOp::Ge => format!("jge @{}\n", label_name),
            CmpOp::G => format!("jg @{}\n", label_name),
            CmpOp::Le => format!("jle @{}\n", label_name),
            CmpOp::L => format!("jl @{}\n", label_name),
            CmpOp::Ne => format!("jnz @{}\n", label_name),
        }
    }

    fn leave_scope_clean(&mut self) {
        let dropped = self.symb_table.exit_scope();
        for val in dropped.iter() {
        }
    }

    

   
    fn new_label(&mut self) -> String {
        let name = format!("label_{}", self.labels.len());
        self.labels.insert(name.clone(), self.sbuf.len());
        let instr = format!("label {}\n", &name);
        self.sbuf.push_str(&instr);
        name
    }

    /// presaves idx but wont push into sbuf
    fn alloc_label(&mut self) -> String {
        let name = format!("label_{}", self.labels.len());
        self.labels.insert(name.clone(), self.sbuf.len());
        name
    }

    /// pushes previously allocated label
    fn push_label(&mut self, name: &str) {
        match self.labels.get_mut(name) {
            Some(v) => {
                *v = self.sbuf.len();
            }
            None => {
                panic!("Can't get label {}!", name);
            }
        }
        self.sbuf.push_str(&format!("label {}\n", name));
    }

    pub fn match_ft_qbf(ft: FType) -> Type {
        match ft {
            FType::int | FType::uint => Type::Long,
            FType::float             => Type::Double,
            FType::bool              => Type::Byte,
            other => todo!("Match ft qbf")
        }
    }

    fn gen_stddat(&mut self) {
        let items = vec![
            (Type::Byte, DataItem::Str(r"%lu\n".into())),
            (Type::Byte, DataItem::Str(r"%ld\n".into())),
            (Type::Byte, DataItem::Str(r"%f\n".into())),
        ];
        self.module.add_data(DataDef::new(
            Linkage::private(),
            "fmt_uint",
            None,
            items[0..1].to_vec()
        ));
        self.module.add_data(DataDef::new(
            Linkage::private(),
            "fmt_int",
            None,
            items[1..2].to_vec()
        ));
        self.module.add_data(DataDef::new(
            Linkage::private(),
            "fmt_float",
            None,
            items[2..3].to_vec()
        ));
    }
    
    fn gen_intrinsic(&mut self, intrin: Intrinsic, rightdat: GenData) 
            -> GenData {
        let mut resd = GenData::new();
        match intrin {
            Intrinsic::Print => {
                // TODO
                match rightdat.qtype {
                    Some(Type::Long) => {
                        if rightdat.ftype == FType::uint {
                            let args = vec![
                                (Type::Long, Value::Global("fmt_uint".into())),
                                (Type::Long, rightdat.val.unwrap_or_else(|| {
                                    panic!("Internal error: expected args \
                                        for print")
                                }))
                            ];

                            resd.instrs.push(
                                Instr::Call(
                                    "printf".into(),
                                    args, 
                                    None
                                )
                            );    
                        } else if rightdat.ftype == FType::int {
                            todo!("finish")  
                        }
                    }        
                    other => todo!("Print for {:?}", other)
                }
            }
            Intrinsic::Len => {
                todo!();
            }
        }
        resd
    }
}

#[derive(Debug)] 
pub struct FuncBuilder {
    pub func: Option<Function>,
    pub ready: bool,
}

impl FuncBuilder {
    pub fn new() -> FuncBuilder {
        FuncBuilder { 
            func: None,
            ready: false,
        }
    }

    pub fn add_instr(&mut self, i: Instr) -> Result<(), ()> {
        if let Some(f) = self.func.as_mut() {
            f.add_instr(i);
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn assign_instr(&mut self, dst: Value, t: Type, i: Instr)
            -> Result<(), ()> {
        if let Some(f) = self.func.as_mut() {
            f.assign_instr(dst, t, i);
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn pop_func(&mut self) -> Option<Function> {
        if !self.ready {
            return None;
        }

        let cl = match &self.func {
            Some(f) => f.clone(),
            None => {return None;}
        };
        self.func = None;
        Some(cl)
    }
}

/// code generation data for each generated expression
#[derive(Debug, Clone)]
pub struct GenData {
    pub symbols: HashMap<String, FSymbol>,
    pub ftype: FType,
    pub cmp_op: Option<CmpOp>,

    pub val: Option<Value>,
    pub qtype: Option<Type>,
   
    pub instrs: Vec<Instr>,

    pub newfunc: Option<Function>,

}

impl GenData {
    pub fn new() -> GenData {
        GenData {
            symbols: HashMap::new(),
            ftype: FType::none,
            cmp_op: None,
            instrs: Vec::new(),
            newfunc: None,
            val: None,
            qtype: None,
        }
    }

    pub fn push_symb(&mut self, s: FSymbol) {
        self.symbols.insert(s.name.clone(), s);
    }
}

#[derive(Debug, Clone)]
pub struct AssignData {
    pub name: String,
    pub t: Type,
    pub val: Instr,
}

impl AssignData {
    pub fn new(name: String, t: Type, val: Instr) -> 
    AssignData {
        AssignData {
            name: name,
            t: t,
            val: val
        }
    }
}

#[derive(Debug, Clone)]
pub struct FSymbTabData {
    pub scope: usize,
    pub name: String,
}

impl FSymbTabData {
    /// usize is scope, string is name
    pub fn new(scope: usize, name: String) -> FSymbTabData {
        FSymbTabData {
            scope: scope,
            name: name,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ArrayData {
    pub id: usize,     
    pub len: usize, 
    pub el_type: FType,
}

impl ArrayData {
    pub fn new(id: usize, len: usize, elt: FType) -> ArrayData {
        ArrayData {
            id: id,
            len: len,
            el_type: elt
        }
    }
}
