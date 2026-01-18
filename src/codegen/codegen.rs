use std::{collections::HashMap, fmt::format, rc::Rc};

use crate::{
    fcparse::fcparse::{self as fparse, AstRoot, CmpOp},
    lexer::lexer::Intrinsic,
    seman::seman::{self as sem, idx_to_ftype, FSymbol, FType, SemAn, SymbolTable, VarPosition},
}; // AstNode;
use fparse::AstNode;
use qbe::{Function, Instr, Linkage, Module, Type, Value};

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
    pub module: Module<'static>,
    alloced_regs: Vec<ValDat>,
    unused_regs: Vec<usize>, // which are unused for some time (lru)
    pub symb_table: SymbolTable,
    predicted_stack: Vec<ValDat>,
    stack_end: usize,               // latest stack frame idx
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
            alloced_regs: vec![ValDat::None; 32],
            unused_regs: Vec::new(),
            symb_table: SymbolTable::new(),
            stack_end: 0,
            predicted_stack: Vec::new(),
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
        let mut res = GenData::new(Vec::new());
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

                {
                    let body_instrs = {
                        let instrs = {
                            let bgd = self.gen_expr(*body).clone();
                            bgd.instrs.clone()
                        };
                        instrs
                    };

                    for instr in body_instrs {
                        func.add_instr(instr);
                    }
                }

                func.add_instr(Instr::Ret(None));
                res.newfunc = Some(func);
            }
            AstNode::ReturnVal { val } => {

            }
            AstNode::CodeBlock { exprs } => {
                for expr in exprs {
                    let gend = self.gen_expr(expr.node);
                    res.instrs.extend(gend.instrs);
                }
            }
            AstNode::Assignment { name, val, ft } => {
                // TODO  
            }
            other => {
                panic!("can't generate yet for {:?}", other);
            }
        }
        if let Some(ref f) = res.newfunc {
            self.module.add_function(f.clone());
        };
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

    pub fn match_ft_qbf(ft: FType) -> Type<'static> {
        match ft {
            FType::int | FType::uint => Type::Long,
            FType::float             => Type::Double,
            FType::bool              => Type::Byte,
            other => todo!("Match ft qbf")
        }
    }

    fn gen_intrinsic(&mut self, intrin: Intrinsic, reg_idx: usize) {
        match intrin {
            Intrinsic::Print => {
                let instrs = format!(
                    "push r1\n\
                                    push r2\n\
                                    push r3\n\
                                    movr r1 r{}\n\
                                    uload r2 2\n\
                                    uload r3 0\n\
                                    ncall 1 r0\n\
                                    pop r3\n\
                                    pop r2\n\
                                    pop r1\n",
                    reg_idx
                );
                self.sbuf.push_str(&instrs);
            }
            Intrinsic::Len => {
                unreachable!();
            }
        }
    }
}

/// code generation data for each generated expression
#[derive(Debug, Clone)]
pub struct GenData {
    pub alloced_regs: Vec<usize>,
    pub symbols: HashMap<String, FSymbol>,
    pub expr_type: FType,
    pub cmp_op: Option<CmpOp>,
    pub arrd: Option<ArrayData>,
   
    pub instrs: Vec<Instr<'static>>,

    pub newfunc: Option<Function<'static>>,
}

impl GenData {
    pub fn new(alloced: Vec<usize>) -> GenData {
        GenData {
            alloced_regs: alloced,
            symbols: HashMap::new(),
            expr_type: FType::none,
            cmp_op: None,
            arrd: None,
            instrs: Vec::new(),
            newfunc: None,
        }
    }

    pub fn push_symb(&mut self, s: FSymbol) {
        self.symbols.insert(s.name.clone(), s);
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
