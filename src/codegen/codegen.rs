use std::{collections::HashMap, fmt::format, rc::Rc};

use crate::{
    fcparse::fcparse::{self as fparse, AstRoot, BinaryOp, CmpOp, UnaryOp},
    lexer::lexer::Intrinsic,
    seman::seman::{self as sem, FSymbol, FType, SemAn, SymbolTable, VarPosition, idx_to_ftype},
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
    tmp_ctr: usize,
    funcs: HashMap<String, FuncData>,
    labels: HashMap<String, usize>, // usize for sbuf idx
    loop_exits: Vec<String>,
    loop_conts: Vec<String>,
    stackidxs: Vec<usize>, // saving last stack idx before function
    overload_ctr: usize,
    matched_overloads: HashMap<usize, (usize, FType)>, // call idx -> overload idx, ret type
}

impl CodeGen {
    pub fn new(ast: Vec<AstRoot>, mo: HashMap<usize, (usize, FType)>) -> CodeGen {
        CodeGen {
            ast: ast,
            cur_ast: 0,
            sbuf: String::new(),
            module: Module::new(),
            fbuild: FuncBuilder::new(),
            should_push: true,
            symb_table: SymbolTable::new(),
            tmp_ctr: 0,
            labels: HashMap::new(),
            loop_exits: Vec::new(),
            loop_conts: Vec::new(),
            stackidxs: Vec::new(),
            overload_ctr: 0,
            matched_overloads: mo,
            funcs: HashMap::new(),
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
                    Linkage::private(), // TODO: pub 
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

                self.should_push = true;
                self.fbuild.ready = true;
            }
            AstNode::ReturnVal { val } => {
                let rightd = self.gen_expr(val.node);

                res.instrs.push(Instr::Ret(rightd.val));
            }
            AstNode::Call { func_name, args, idx } => {
                // call idx
                let mut gends: Vec<GenData> = Vec::new();
                for arg in args {
                    let gd = self.gen_expr(arg.node);
                    gends.push(gd);
                }

                let mut args_qbe = Vec::new();
                for gd in gends {
                    args_qbe.push((
                        Self::match_ft_qbf(gd.ftype),
                        gd.val.unwrap_or_else(|| {
                            panic!("args incomplete val")
                        })
                    ));
                }

                let (ov_idx, ret_type) = match self
                        .matched_overloads.get(&idx) {
                    Some(f) => {
                        f.clone()
                    }   
                    None => {
                        panic!("Can't get ret type for func call")
                    }
                };

                let instr = Instr::Call(
                        format!("{}_{}", func_name, ov_idx), 
                        args_qbe, 
                        None
                );
                let tmpvar = self.new_temp();

                res.val = Some(tmpvar.clone());
                res.ftype = ret_type;
                
                res.instrs.push(Instr::Assign(
                    tmpvar, 
                    Self::match_ft_qbf(ret_type), 
                    Box::new(instr)
                ));
            }
            AstNode::CodeBlock { exprs } => {
                self.symb_table.enter_scope();
                for expr in exprs {
                    let gend = self.gen_expr(expr.node);
                    res.instrs.extend(gend.instrs);
                }
                self.symb_table.exit_scope();
            }
            AstNode::Assignment { name, val, ft } => {
                let mut rdat = self.gen_expr(*val);
                res.instrs.extend(rdat.instrs.drain(..));

                res.instrs.extend(rdat.instrs.drain(..));
                let val = rdat.val.unwrap_or_else(|| {
                    panic!("Internal error: can't get val of \
                        assignment")
                });
                

                self.symb_table.newsymb(
                    FSymbol::new(
                        name.clone(), 
                        VarPosition::None, // obsolete, TODO: delete  
                        ft
                    )
                );

                res.instrs.push(
                    Instr::Assign(
                        Value::Temporary(name), 
                        Self::match_ft_qbf(ft), 
                        Box::new(Instr::Copy(val))
                    )
                );
            }
            
            AstNode::Uint(uv) => {
                let val = Value::Const(uv); 
                res.val = Some(val);
                res.qtype = Some(Type::Long);
                res.ftype = FType::uint;
            }
            AstNode::Int(iv) => {
                let val = Value::Const(iv as u64); 
                res.val = Some(val);
                res.qtype = Some(Type::Long);
                res.ftype = FType::int;
            }
            AstNode::Float(fv) => {
                let val = Value::double(fv);
                res.val = Some(val);
                res.qtype = Some(Type::Double);
                res.ftype = FType::float;
            }
            AstNode::UnaryOp { op, expr } => {
                let mut gd = self.gen_expr(*expr);
                res.instrs.extend(gd.instrs.extract_if(.., |x| 
                    {
                        matches!(x, Instr::Assign(_, _, _))
                    }
                ));

                let tmp = self.new_temp();

                match op {
                    UnaryOp::Negate => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(),
                            Self::match_ft_qbf(gd.ftype),
                            Box::new(Instr::Neg(
                                gd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::Not => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(gd.ftype), 
                            Box::new(Instr::Xor( 
                                gd.val.unwrap(), 
                                Value::Const(u64::MAX)
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::LogicalNot => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(gd.ftype), 
                            Box::new(Instr::Cmp( 
                                Self::match_ft_qbf(gd.ftype),
                                qbe::Cmp::Eq,
                                gd.val.unwrap(), 
                                Value::Const(0)
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = gd.ftype;
                    }
                    other => todo!("unary op {:#?}", other)
                }
            }
            AstNode::BinaryOp { op, left, right } => {
                let mut leftd = self.gen_expr(*left);
                res.instrs.extend(leftd.instrs.extract_if(.., |x| 
                    {
                        matches!(x, Instr::Assign(_, _, _))
                    }
                ));

                let mut rightd = self.gen_expr(*right);
                res.instrs.extend(rightd.instrs.extract_if(.., |x| 
                    {
                        matches!(x, Instr::Assign(_, _, _))
                    }
                ));

                let tmp = self.new_temp();

                match op {
                    fparse::BinaryOp::Add => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(leftd.ftype), 
                            Box::new(Instr::Add(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
                    }
                    fparse::BinaryOp::Substract => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(leftd.ftype), 
                            Box::new(Instr::Sub(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
                    }
                    fparse::BinaryOp::Multiply => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(leftd.ftype), 
                            Box::new(Instr::Mul(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
                    }
                    fparse::BinaryOp::Divide => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(leftd.ftype), 
                            Box::new(Instr::Div(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;                    
                    }
                    fparse::BinaryOp::Remainder => {
                        res.instrs.push(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(leftd.ftype), 
                            Box::new(Instr::Rem(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
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
            AstNode::Variable(var) => { // var name
                let var_dat = self.symb_table.get(var.clone()).unwrap_or_else(|| {
                    panic!("Internal: Can't get variable {}", var)
                });

                res.ftype = var_dat.1.ftype;
                res.qtype = Some(Self::match_ft_qbf(var_dat.1.ftype));
                res.val = Some(Value::Temporary(var.clone()));

                res.instrs.push(
                    Instr::Load(
                        Self::match_ft_qbf(var_dat.1.ftype), 
                        Value::Temporary(var.clone())
                    )
                );
            }
            AstNode::VariableCast { name, target_type } => {
                let symb = self.symb_table.get(name.clone()).unwrap();

                let ft_src = symb.1.ftype;
                let tmp = self.new_temp();
                
                let conv_instr = match (ft_src, target_type) {
                    (FType::float, FType::uint) => { // bitwise repr
                        res.ftype = FType::uint;
                        Instr::Dtoui(
                            Value::Temporary(name.clone())
                        )
                    }
                    (FType::float, FType::int) => { // bitwise repr
                        res.ftype = FType::int;
                        Instr::Dtosi(
                            Value::Temporary(name.clone())
                        )
                    }
                    (FType::uint, FType::float) => {
                        res.ftype = FType::float;
                        Instr::Ultof(
                            Value::Temporary(name.clone())
                        )
                    }
                    (FType::int, FType::float) => {
                        res.ftype = FType::float;
                        Instr::Sltof(
                            Value::Temporary(name.clone())
                        )
                    }
                    (FType::int, FType::uint) => {
                        res.ftype = FType::uint;
                        Instr::Copy(
                            Value::Temporary(name.clone())
                        )
                    }
                    (FType::uint, FType::int) => {
                        res.ftype = FType::int;
                        Instr::Copy(
                            Value::Temporary(name.clone())
                        )
                    }
                    other => unimplemented!("Type conv: {:?} => {:?}",
                        ft_src, target_type)
                };

                res.instrs.push(Instr::Assign(
                    tmp.clone(),
                    Self::match_ft_qbf(target_type),
                    Box::new(conv_instr)
                ));

                res.val = Some(tmp);
            }
            AstNode::Reassignment { name, newval } => {
                let mut gd = self.gen_expr(newval.node);
                res.instrs.extend(gd.instrs.extract_if(.., |x| {
                    matches!(x, Instr::Assign(_, _, _))
                }));

                let val = Value::Temporary(name.clone());

                res.instrs.push(Instr::Assign(
                    val.clone(),
                    Self::match_ft_qbf(gd.ftype), 
                    Box::new(Instr::Copy(gd.val.unwrap_or_else(|| {
                        panic!("Internal: can't get reas value")
                    })))
                ));

                res.val = Some(val);
                res.ftype = gd.ftype;
            }
            AstNode::none => {}
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

    fn new_temp(&mut self) -> Value {
        let name = format!("tmp_{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        Value::Temporary(name)
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
            other => todo!("Match ft qbf for {:?}", ft)
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
                            let args = vec![
                                (Type::Long, Value::Global("fmt_int".into())),
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
                        }
                    }
                    Some(Type::Double) => {
                        let args = vec![
                            (Type::Long, Value::Global("fmt_float".into())),
                            (Type::Double, rightdat.val.unwrap_or_else(|| {
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
    //pub tmpname: Option<String>, 
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
pub struct FuncData {
    pub name: String,
    pub ret_type: FType,
}

impl FuncData {
    pub fn new(name: String, t: FType) -> 
    FuncData {
        FuncData {
            name: name,
            ret_type: t,
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
