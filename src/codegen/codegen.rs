use std::{backtrace::Backtrace, collections::{HashMap, HashSet}, ptr::hash, sync::{Arc, Mutex, RwLock}};

use crate::{
    cli::Target, fcparse::fcparse::{self as fparse, AstRoot, Attr, CmpOp, FuncArg, FuncTable, UnaryOp}, lexer::lexer::Intrinsic, seman::seman::{FSymbol, FType, OverloadTable, StructTable, SymbolTable, VarPosition}
}; // AstNode;
use fparse::AstNode;
use indexmap::IndexSet;
use qbe::{DataDef, DataItem, Function, Instr, Linkage, Module, Type, TypeDef, Value};

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
    ast: Arc<Vec<AstRoot>>,
    cur_ast: usize,
    pub sbuf: String,
    pub module: Module,
    pub fbuild: FuncBuilder,
    pub symb_table: SymbolTable,
    func_tab: Arc<FuncTable>,
    struct_tab: Arc<StructTable>,
    should_push: bool,
    tmp_ctr: usize,
    dslbl_ctr: usize,
    funcs: HashMap<String, FuncData>,
    labels: HashMap<String, usize>, // usize for sbuf idx
    loop_exits: Vec<String>,
    loop_conts: Vec<String>,
    matched_overloads: OverloadTable, // call idx -> overload idx, ret type
    need_addr: bool,
    expected_type: FType,
    usedmods: Vec<String>,
    curmod: String,
    target: Target,
    genfuncs: Arc<HashMap<String, AstRoot>>, // generic functions 
    deffered_gen: Vec<AstRoot>, // for generics mostly
    pub prev_gen: Arc<RwLock<IndexSet<String>>>, // which generic functions were already generated 
}

impl CodeGen {
    pub fn new(ast: Arc<Vec<AstRoot>>, mo: OverloadTable, first: bool,
        fnctb: Arc<FuncTable>, struct_tab: Arc<StructTable>, tgt: Target,
        genfuncs: Arc<HashMap<String, AstRoot>>, prev_gen: Arc<RwLock<IndexSet<String>>>) 
        -> CodeGen {
        CodeGen {
            ast: ast,
            cur_ast: 0,
            sbuf: String::new(),
            module: Module::new(),
            fbuild: FuncBuilder::new(),
            func_tab: fnctb,
            struct_tab: struct_tab,
            should_push: true,
            symb_table: SymbolTable::new(),
            tmp_ctr: 0,
            dslbl_ctr: 0,
            labels: HashMap::new(),
            loop_exits: Vec::new(),
            loop_conts: Vec::new(),
            matched_overloads: mo,
            funcs: HashMap::new(),
            need_addr: false,
            expected_type: FType::none,
            usedmods: Vec::new(),
            curmod: "main".into(),
            target: tgt,
            genfuncs,
            deffered_gen: Vec::new(),
            prev_gen: prev_gen,
        }
    }

    fn get_use_paths(&mut self) -> Vec<String> {
        let mut res = Vec::new();
        res.push(self.curmod.clone());
        res.extend(self.usedmods.iter().cloned());
        res
    }

    pub fn gen_everything(&mut self, nomain: bool) {
        self.gen_stddat();
        let mut had_main = false;
       
        while let Some(r) = self.ast.get(self.cur_ast) {
            if !self.should_gen(&r) {
                self.cur_ast += 1;
                continue;
            }

            let node_cl = r.node.clone();
            let mut was_func = false;
            if let AstNode::Function { name, ret_type, .. } = &node_cl {
                was_func = true;
                if (name.path_to_string() == "main::main") && (!had_main) && 
                    (!nomain) {
                    had_main = true;
                    self.gen_prologue(ret_type.clone());
                }
            };
            
            let _gdat = self.gen_expr(node_cl);
            self.cur_ast += 1;

            if !self.deffered_gen.is_empty() && was_func {
                let ars: Vec<AstRoot> = self.deffered_gen.drain(..).collect(); 
                for ar in ars {
                    let name = ar.node.get_func_name();

                    let already_generated = {
                        let lock = self.prev_gen.read().unwrap();
                        lock.contains(&name)
                    };
                    if already_generated {
                        continue;
                    }

                    self.gen_expr(ar.node);

                    let mut lock = self.prev_gen.write().unwrap();
                    lock.insert(name);
                }
            }
        }
        
    }

    pub fn write_file(&mut self, fname: &str) -> Result<(), std::io::Error> {
        if let Some(parent) = std::path::Path::new(fname).parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(fname, &format!("{}", self.module))?;

        Ok(())
    }

    /// Generates prologue (main func)
    /// Check ret type first!
    fn gen_prologue(&mut self, ret_type: FType) {
        let main_args = vec![
            (Type::Word, Value::Temporary("argc".to_owned())),
            (Type::Long, Value::Temporary("argv".to_owned()))
        ];
        let mut mainf = Function::new(
            Linkage::public(), 
            "main",
            main_args.clone(),
            Some(Type::Word)
        );

        mainf.add_block("start");
        if ret_type != FType::none {
            let tmp = self.new_temp();
            mainf.assign_instr(
                tmp.clone(),
                Self::match_ft_qbf_t(&ret_type, true),
                Instr::Call("main_main_0".into(), main_args, None)
            );
            mainf.add_instr(Instr::Ret(Some(tmp)));
        } else {
            mainf.add_instr(
                Instr::Call("main_main_0".into(), main_args, None)
            );
            mainf.add_instr(Instr::Ret(Some(Value::Const(0))));
        }

        self.module.add_function(mainf);
    }

    fn gen_expr(&mut self, node: AstNode) -> GenData {
        let mut res = GenData::new();
        match node {
            AstNode::Function { name, args, ret_type, body, public } => {
                let generics = name.get_generics();
                if !generics.is_empty() {
                    return res;
                }

                self.gen_func(&name, args, ret_type, body, 0, public); 
            }
            AstNode::FunctionOverload { func, idx, public } => {
                let (name, args, ret_type, body) = match *func {
                    AstNode::Function { name, args, ret_type, body, public: _ } => {
                        (name, args, ret_type, body)
                    }
                    _other => unreachable!()
                };

                let generics = name.get_generics();
                if !generics.is_empty() {
                    return res;
                }

                self.gen_func(&name, args, ret_type, body, idx, public); 
            }
            AstNode::ReturnVal { val } => {
                let rightd = self.gen_expr(val.node);
                let ret_val = if matches!(rightd.ftype, FType::Struct(_)) {
                    // if stack struct being returned, do sret
                    let snm = rightd.ftype.if_struct().unwrap();
                    let (tot_size, max_al) = self.get_struct_size(&snm);

                    let to_ptr = self.fbuild.args_passed.get(0)
                        .unwrap()
                        .name
                        .clone()
                        ;
                    let to_val = Value::Temporary(to_ptr);

                    let args = vec![
                        (Type::Long, to_val.clone()), //dst 
                        (Type::Long, rightd.val.clone().unwrap()), // src 
                        (Type::Long, Value::Const(tot_size as u64))
                    ];
                    
                    self.fbuild.add_instr(Instr::Call(
                        "memcpy".into(),
                        args,
                        None
                    ));
                    
                    Some(to_val)
                } else {
                    rightd.val.clone()
                };

                res.returned = true;

                let dropped = self.symb_table.to_drop();
                let mut except = Vec::new();
                if let Some(ref v) = rightd.val {
                    except.push(v.clone());
                };

                self.leave_scope_clean(&dropped, except);

                self.fbuild.add_instr(Instr::Ret(ret_val));
                self.symb_table.exit_scope();
            }
            AstNode::Call { func_name, args, idx } => {
                let (ov_idx, ret_type) = match self
                        .matched_overloads.get(&idx) {
                    Some(f) => {
                        f.clone()
                    }   
                    None => {
                        panic!("Can't get ret type for func call")
                    }
                };

                let paths = self.get_use_paths();
                let mut func_dat = self.func_tab
                    .get_func(&func_name.path_to_string(), &paths)
                    .unwrap()
                    .get(ov_idx.unwrap())
                    .unwrap()
                    .clone();

                let mut args_qbe = Vec::new();
                let mut args_ft = Vec::new(); // vec of args ftypes (for generics)

                match func_dat.ret_type {
                    FType::Struct(snm) => {
                        let (size, al) = self.get_struct_size(&snm);

                        let stack_tmp = self.new_temp();
                        self.fbuild.assign_instr(
                            stack_tmp.clone(),
                            Type::Long,
                            Self::allocalign(size, al)
                        );

                        args_qbe.push((Type::Long, stack_tmp.clone()));
                    }
                    other => {}
                };

                for (idx, arg) in args.iter().enumerate() {
                    self.expected_type = func_dat.args
                        .get(idx)
                        .unwrap()
                        .ftype
                        .clone();
                    let old_needaddr = self.need_addr;
                    self.need_addr = false;

                    let gd = self.gen_expr(arg.node.clone());
                    self.expected_type = FType::none;
                    self.need_addr = old_needaddr;
                    
                    args_ft.push(gd.ftype.clone());
                    let mut qtype = Self::match_ft_qbf(&gd.ftype);
                    if let Some(a) = func_dat.args.get(idx) {
                        match &a.ftype {
                            FType::Struct(name) => {
                                // we would need only name here so other 
                                // fields doesnt matter
                                qtype = Type::Aggregate(TypeDef {
                                    name: name.to_owned().replace("::", "_"), 
                                    align: None, 
                                    items: Vec::new()
                                });
                            },
                            _other => {}
                        }
                    };

                    args_qbe.push((
                        qtype,
                        gd.val.unwrap_or_else(|| {
                            panic!("args incomplete val")
                        })
                    ));
                }

                let generics = func_dat.name.get_generics();
                let generated_fname = match generics.is_empty() {
                    false => {
                        let res = self.gen_generic_func(
                            &func_dat.name.path_to_string(),
                            args_ft,
                            &self.expected_type.clone()
                        );
                        Some(res)
                    }
                    true => None,
                }; 
                

                let mut has_rn = false;
                let mname: String = match self.func_tab
                        .get_func(&func_name.path_to_string(), &paths) {
                    Some(v) => {
                        let fin_idx = match ov_idx {
                            Some(v) => v,
                            None => 0
                        };

                        let f = v.get(fin_idx);
                        let unf = f.unwrap();
                        has_rn = unf.real_name.is_some();
                        unf.real_name.
                            clone().
                            unwrap_or(
                                unf.name.path_to_segs().join("_")
                            )
                    }  
                    None => {
                        func_name.path_to_segs().join("_")
                    }
                };

                let name = match (ov_idx, generated_fname.is_some()) {
                    (_, true) => generated_fname.unwrap(),
                    (Some(v), false) if !has_rn => format!("{}_{}", mname, v),
                    _other => format!("{}", mname)
                };

                let instr = Instr::Call(
                    name, 
                    args_qbe, 
                    None
                );
                let tmpvar = self.new_temp();

                res.val = Some(tmpvar.clone());
                res.ftype = ret_type.clone();
                
                if ret_type != FType::none {
                    self.fbuild.add_instr(Instr::Assign(
                        tmpvar, 
                        Self::match_ft_qbf(&ret_type), 
                        Box::new(instr)
                    ));
                } else {
                    self.fbuild.add_instr(instr);
                }
            }
            AstNode::CodeBlock { exprs } => {
                self.symb_table.enter_scope();
                for expr in exprs {
                    if !self.should_gen(&expr) {
                        continue;
                    }
                    let gend = self.gen_expr(expr.node.clone());
                    res.instrs.extend(gend.instrs);
                    res.returned = gend.returned;
                }
               
                if !res.returned && self.fbuild.func.is_some() {
                    let dropped = self.symb_table.exit_scope();
                    self.leave_scope_clean(&dropped, Vec::new());
                } else if !res.returned {
                    self.symb_table.exit_scope();
                }
            }
            AstNode::Assignment { name, val, ft } => {
                let owner = match &*val {
                    AstNode::Call { func_name, args, idx } => true,
                    AstNode::StructCreate { name, field_vals } => true,
                    other => false,
                };

                self.need_addr = true;
                self.expected_type = ft.clone();
                let rdat = self.gen_expr(*val);
                self.expected_type = FType::none;
                self.need_addr = false;

                let val = rdat.val.unwrap_or_else(|| {
                    panic!("Internal error: can't get val of \
                        assignment")
                });
                
                let res_ft = match rdat.ftype {
                    FType::none | FType::nil => ft.clone(),
                    other => other
                };
                res.ftype = res_ft.clone();

                let mut symb = FSymbol::new(
                    name.clone(), 
                    VarPosition::None, // obsolete, TODO: delete  
                    res_ft.clone()
                );
                symb.owner = owner;

                self.symb_table.newsymb(symb);

                self.fbuild.assign_instr(
                    Value::Temporary(name), 
                    Self::match_ft_qbf(&res_ft), 
                    Instr::Copy(val)
                );
            }
            
            AstNode::Uint(uv) => {
                let val = Value::Const(uv); 
                res.val = Some(val);
                res.qtype = Some(Type::Long);
                res.ftype = FType::uint;
            }
            AstNode::Int(iv) => {
                let val = Value::SignConst(iv); 
                res.val = Some(val);
                res.qtype = Some(Type::Long);
                res.ftype = FType::int;
            }
            AstNode::Double(fv) => {
                let val = Value::double(fv);
                res.val = Some(val);
                res.qtype = Some(Type::Double);
                res.ftype = FType::double;
            }
            AstNode::Single(sv) => {
                let val = Value::float(sv);
                res.val = Some(val);
                res.ftype = FType::single;
            }
            AstNode::boolVal(bv) => {
                let val = Value::Const(bv as u64);
                res.val = Some(val);
                res.ftype = FType::bool;
            }
            AstNode::I32(iwv) => {
                let val = Value::SignConst(iwv as i64);
                res.val = Some(val);
                res.ftype = FType::i32;
            }
            AstNode::U32(uwv) => {
                let val = Value::Const(uwv as u64);
                res.val = Some(val);
                res.ftype = FType::u32;
            }
            AstNode::Ishort(ihv) => {
                let val = Value::SignConst(ihv as i64);
                res.val = Some(val);
                res.ftype = FType::ishort;
            }
            AstNode::Ushort(ihv) => {
                let val = Value::Const(ihv as u64);
                res.val = Some(val);
                res.ftype = FType::ushort;
            }
            AstNode::Ibyte(ibv) => {
                let val = Value::SignConst(ibv as i64);
                res.val = Some(val);
                res.ftype = FType::ibyte;
            }
            AstNode::Ubyte(ubv) => {
                let val = Value::Const(ubv as u64);
                res.val = Some(val);
                res.ftype = FType::ubyte;
            }

            AstNode::StringLiteral(st) => {
                let st_name = self.new_dslab();
                let len = st.len();

                let items = vec![
                    (Type::Byte, DataItem::Str(st)),
                    (Type::Byte, DataItem::Const(0))
                ];

                self.module.add_data(DataDef { 
                    linkage: Linkage::private(), // TODO: pub (maybe)
                    name: st_name.clone(), 
                    align: Some(8), 
                    items: items
                });

                let mut symb = FSymbol::new(
                    st_name.clone(),
                    VarPosition::None, // obsolete 
                    FType::strconst
                );
                symb.len = Some(len);
                symb.dsname = Some(st_name.clone());
                self.symb_table.newsymb(symb);

                res.val = Some(Value::Global(st_name));
                res.ftype = FType::strconst;
            }
            AstNode::Array(ft, elems) => {
                let (mut el_size, agg) = match &ft {
                    FType::Struct(sn) => {
                        let paths = self.get_use_paths();
                        let dat = self.struct_tab.get(&sn, &paths).unwrap();
                        (dat.size as u64, Some(sn.clone()))
                    }
                    other => (0, None)
                }; 

                let tmp = self.new_temp();

                let mut total_size: u64 = 0;
                let mut vals = Vec::new();

                for el in elems {
                    if let AstNode::ArrRep(n) = el {
                        let prefix_len = vals.len(); // everything so far
                        for _ in 1..n {
                            vals.extend(vals[0..prefix_len].to_vec());
                        }
                        
                        total_size *= n;

                        continue;
                    };

                    let gd = self.gen_expr(el);
                    vals.push(gd.val.clone().unwrap());
                    if el_size == 0 {
                        el_size = Self::sizeof(&gd.ftype);
                    }
                    total_size += el_size;
                }

                res.ftype = FType::Array(
                    Box::new(ft.clone()),
                    vals.len()
                );

                self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Alloc8(total_size)
                );

                let qtype = Self::match_ft_qbf(&ft);
                let idx_tmp = self.new_temp();
                for (i, v) in vals.iter().enumerate() { 
                    self.fbuild.assign_instr(
                        idx_tmp.clone(),
                        Type::Long,
                        Instr::Add(
                            tmp.clone(), 
                            Value::Const(i as u64 * el_size)
                        )
                    );

                    if let Some(sn) = &agg {
                        // If dense array, rely on libc memcpy or copy if present 
                        let args = vec![
                            (Type::Long, idx_tmp.clone()),
                            (Type::Long, v.clone()),
                            (Type::Long, Value::Const(el_size))
                        ];

                        let clone_tmp = self.new_temp();
                        self.fbuild.assign_instr(
                            clone_tmp.clone(),
                            Type::Long,
                            Instr::Call(
                                "memcpy".into(),
                                args,
                                None 
                            )
                        );
                        // Original value will be dropped at the end of scope
                    } else {
                        self.fbuild.add_instr(Instr::Store(
                            qtype.clone(),
                            idx_tmp.clone(),
                            v.clone()
                        ));
                    }
                }

                res.val = Some(tmp);
            }
            AstNode::ArrayElem(arr, idx_val) => {
                let old_needaddr = self.need_addr;
                self.need_addr = true;
                let val_dat  = self.gen_expr(*arr);
                self.need_addr = old_needaddr;

                let idx_gd   = self.gen_expr(idx_val.node);
                let tmp      = self.new_temp();

                // agg - whether element ftype is aggregate (dense array)
                let (el_ftype, agg) = match val_dat.ftype {
                    FType::Array(el, _ctr) => {
                        let res = *el.clone();
                        let agg = match &res {
                            FType::Struct(s) => Some(s.clone()),
                            other => None,
                        };
                        (res, agg)
                    }
                    FType::strconst => (FType::ubyte, None), // byte-wise indexing
                    _other => unreachable!()
                };

                let el_size  = match &agg {
                    Some(v) => {
                        let paths = self.get_use_paths();
                        let dat = self.struct_tab.get(&v, &paths).unwrap();
                        dat.size as u64
                    } 
                    None => Self::sizeof(&el_ftype)
                };

                self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Mul(idx_gd.val.unwrap(), Value::Const(el_size))
                );
               
                self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Add(tmp.clone(), val_dat.val.unwrap().clone())
                );
                
                res.by_addr = self.need_addr || agg.is_some();
                if !res.by_addr {
                    let el_qtype = Self::match_ft_qbf_t(&el_ftype, true);
                    self.fbuild.assign_instr(
                        tmp.clone(),
                        Type::Long,
                        Instr::Load(el_qtype, tmp.clone())
                    );
                }

                res.val   = Some(tmp);
                res.ftype = match agg {
                    Some(nm) => FType::StructPtr(nm),
                    None     => el_ftype
                };
            }
            AstNode::UnaryOp { op, expr } => {
                let mut gd = self.gen_expr(*expr);
                res.instrs.extend(gd.instrs.extract_if(.., |x| 
                    {
                        matches!(x, Instr::Assign(_, _, _))
                    }
                ));

                let tmp = self.new_temp();
                res.val = Some(tmp.clone());

                match op {
                    UnaryOp::Negate => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(),
                            Self::match_ft_qbf(&gd.ftype),
                            Box::new(Instr::Neg(
                                gd.val.unwrap()
                            ))
                        ));
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::Not => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(&gd.ftype), 
                            Box::new(Instr::Xor( 
                                gd.val.unwrap(), 
                                Value::Const(u64::MAX)
                            ))
                        ));
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::LogicalNot => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(&gd.ftype), 
                            Box::new(Instr::Cmp( 
                                Self::match_ft_qbf(&gd.ftype),
                                qbe::Cmp::Eq,
                                gd.val.unwrap(), 
                                Value::Const(0)
                            ))
                        ));
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::AddressOf => {
                        // doesnt actually do anything since 
                        // struct is already a pointer
                        let _name = match &gd.val {
                            Some(Value::Temporary(name)) | Some(Value::Global(name))
                                => name.clone(),
                            other => panic!("Expected var, found {:?}", other)
                        };

                        res.ftype = gd.ftype;
                        res.val = gd.val;
                    }
                    UnaryOp::Deref => {
                        let ftype_exp = match &self.expected_type {
                            FType::none => match gd.ftype {
                                FType::StructPtr(s) | FType::StructHeapPtr(s) => 
                                    FType::Struct(s),
                                other => panic!("Deref of type {}", other)
                            },
                            other => other.clone(),
                        };
                        let (qtype_exp, instr) = match Self::match_ft_qbf_t(
                            &ftype_exp, 
                            true
                        ) {
                            Type::Aggregate(_) => (
                                Type::Long, // ptr
                                Instr::Copy(gd.val.clone().unwrap())
                            ),
                            other => (
                                other.clone(),
                                Instr::Load(
                                    other,
                                    gd.val.clone().unwrap()
                                )
                            ), 
                        };

                        self.fbuild.assign_instr(
                            tmp.clone(),
                            qtype_exp.clone(),
                            instr 
                        );
                        res.ftype = ftype_exp;
                    }
                    other => todo!("unary op {:#?}", other)
                }
            }
            AstNode::BinaryOp { op, left, right } => {
                let leftd = self.gen_expr(*left);
                let rightd = self.gen_expr(*right);

                let tmp = self.new_temp();

                match op {
                    fparse::BinaryOp::Add => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(&leftd.ftype), 
                            Box::new(Instr::Add(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
                    }
                    fparse::BinaryOp::Substract => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(&leftd.ftype), 
                            Box::new(Instr::Sub(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
                    }
                    fparse::BinaryOp::Multiply => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(&leftd.ftype), 
                            Box::new(Instr::Mul(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
                    }
                    fparse::BinaryOp::Divide => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(&leftd.ftype), 
                            Box::new(Instr::Div(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;                    
                    }
                    fparse::BinaryOp::Remainder => {
                        self.fbuild.add_instr(Instr::Assign(
                            tmp.clone(), 
                            Self::match_ft_qbf(&leftd.ftype), 
                            Box::new(Instr::Rem(
                                leftd.val.unwrap(), 
                                rightd.val.unwrap()
                            ))
                        ));
                        res.val = Some(tmp);
                        res.ftype = leftd.ftype;
                    }
                    fparse::BinaryOp::Compare(cmp_op) => {
                        let val = self.gen_cmp_op(
                            cmp_op, 
                            leftd, 
                            rightd
                        );
                        res.val = Some(val);
                        res.ftype = FType::bool;
                    }
                    other => todo!("{:?}", other)
                }
            }
            AstNode::Intrinsic { intr, val } => {
                let need_addr_old = self.need_addr;
                self.need_addr = false;
                let gend = self.gen_expr(*val);
                self.need_addr = need_addr_old;
                
                let ind = self.gen_intrinsic(intr, gend);
                res.ftype = ind.ftype;
                res.val = ind.val;
            }
            AstNode::Variable(var) => { // var name
                let paths = self.get_use_paths();
                if let Some(v) = self.struct_tab.get(&var, &paths) {
                    res.ftype = FType::Struct(v.name.clone());
                    return res;
                };

                // TODO: func ptrs

                let var_dat = self.symb_table.get(&var).unwrap_or_else(|| {
                    panic!("Internal: Can't get variable {}", var)
                });

                res.ftype = var_dat.1.ftype.clone();
                res.qtype = Some(Self::match_ft_qbf(&var_dat.1.ftype));
                res.val = Some(Value::Temporary(var.clone()));
            }
            AstNode::VariableCast { name, target_type } => {
                res.ftype = target_type.clone();
                let tmp = self.new_temp();
                let symb = self.symb_table.get(&name).unwrap();

                match (&symb.1.ftype, &target_type) {
                    (FType::Ptr, FType::StructPtr(_)) | (FType::Ptr, FType::Struct(_)) |
                        (FType::Ptr, FType::StructHeapPtr(_)) | 
                        (FType::StructHeapPtr(_), FType::StructPtr(_)) => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            Type::Long,
                            Instr::Copy(Value::Temporary(name.clone()))
                        );
                        res.val = Some(tmp.clone());
                        return res;
                    }
                    _other => {}
                };

                let ft_src = symb.1.ftype.clone();
                
                let conv_instr = Self::get_conv(
                    &ft_src, 
                    &target_type, 
                    Value::Temporary(name.clone())
                );

                // QBE doesnt like byte assignments
                let tgt_qtype = match Self::match_ft_qbf(&target_type) {
                    Type::Byte | Type::UnsignedByte | Type::SignedByte => {
                        Type::Word
                    }
                    other => other
                };

                self.fbuild.add_instr(Instr::Assign(
                    tmp.clone(),
                    tgt_qtype,
                    Box::new(conv_instr)
                ));

                res.val = Some(tmp);
            }
            AstNode::ExprCast { expr, target_type } => {
                res.ftype = target_type.clone();
                let gd = self.gen_expr(*expr);
                match (&gd.ftype, &target_type) {
                    (FType::Ptr, FType::StructPtr(_)) | (FType::Ptr, FType::Struct(_)) |
                        (FType::Ptr, FType::StructHeapPtr(_)) |
                        (FType::StructHeapPtr(_), FType::StructPtr(_)) => {
                        res.val = gd.val.clone();
                        return res;
                    }
                    _other => {}
                };
                let tmp = self.new_temp();

                let conv = Self::get_conv(
                        &gd.ftype, 
                        &target_type, 
                        gd.val.unwrap()
                );
                
                let tgt_qtype = match Self::match_ft_qbf(&target_type) {
                    Type::Byte | Type::UnsignedByte | Type::SignedByte => {
                        Type::Word
                    }
                    other => other
                };

                self.fbuild.add_instr(Instr::Assign(
                        tmp.clone(), 
                        tgt_qtype,
                        Box::new(conv)
                ));

                res.ftype = target_type;
                res.val = Some(tmp);
            }
            AstNode::Reassignment { name, idx, newval } => {
                self.need_addr = true;
                let leftdat = self.gen_expr(*name);
                self.need_addr = false;
                let val = leftdat.val.expect(
                    "expected value for left side",
                );

                let gd = self.gen_expr(newval.node);

                match (leftdat.ftype, &gd.ftype) {
                    (other, FType::Struct(_)) if leftdat.by_addr => {
                        self.gen_array_store(
                            &gd.ftype, 
                            None, 
                            &gd.val.unwrap(),
                            &val
                        ); 
                    }
                    (other, _) if leftdat.by_addr => {
                        // type dst val 
                        let qtype = Self::match_ft_qbf_tl(&gd.ftype, true, true);
                        self.fbuild.add_instr(Instr::Store(
                            qtype, 
                            val.clone(),
                            gd.val.expect("Internal: can't get reas value"), 
                        ));
                    }
                    (_other, _) => {
                        self.fbuild.add_instr(Instr::Assign(
                            val.clone(),
                            Self::match_ft_qbf(&gd.ftype), 
                            Box::new(Instr::Copy(gd.val.unwrap_or_else(|| {
                                panic!("Internal: can't get reas value")
                            })))
                        ));
                    }
                }

                res.val = Some(val);
                res.ftype = gd.ftype;
            }
            AstNode::IfStatement { cond, if_true, if_false } => {
                let cond_gd = self.gen_expr(cond.node);

                let cond_val_tmp = self.new_temp();
                self.fbuild.add_instr(Instr::Assign(
                    cond_val_tmp.clone(),
                    Type::Long,
                    Box::new(Instr::Extub(cond_gd.val.unwrap()))
                ));

                let cond_res_tmp = self.new_temp();
                let cmp_instr = Instr::Cmp(
                    Type::Long,
                    qbe::Cmp::Eq,
                    cond_val_tmp,
                    Value::Const(1)
                );
                self.fbuild.add_instr(Instr::Assign(
                    cond_res_tmp.clone(),
                    Type::Long,
                    Box::new(cmp_instr)
                ));

                let true_lab  = self.alloc_label();
                let false_lab = self.alloc_label();
                let endif     = self.alloc_label();

                let false_to = if if_false.is_some() {
                    false_lab.clone()
                } else {
                    endif.clone()
                };

                self.fbuild.add_instr(Instr::Jnz(
                        cond_res_tmp, 
                        true_lab.clone(), // if true  
                        false_to // if false
                ));

                self.fbuild.add_block(true_lab);

                let true_gd = self.gen_expr(if_true.node);
                res.instrs.extend(true_gd.instrs);
                if !true_gd.returned { 
                    self.fbuild.add_instr(Instr::Jmp(endif.clone()));
                }

                if let Some(n) = if_false {
                    self.fbuild.add_block(false_lab);
                    let false_gd = self.gen_expr(n.node);
                    res.instrs.extend(false_gd.instrs);
                }

                self.fbuild.add_block(endif);

                // TODO: if returning smth, like in rust
            }
            AstNode::WhileLoop { cond, body } => {
                let loop_block = self.alloc_label();
                self.loop_conts.push(loop_block.clone());

                // safety, since qbe usually needs jmp/ret at the block end
                self.fbuild.add_instr(Instr::Jmp(loop_block.clone()));
                self.fbuild.add_block(loop_block.clone());
                
                let end     = self.alloc_label();
                self.loop_exits.push(end.clone());
                let body_lbl = self.alloc_label();

                let cond_gd = self.gen_expr(cond.node);

                let cond_val_tmp = self.new_temp();
                self.fbuild.add_instr(Instr::Assign(
                    cond_val_tmp.clone(),
                    Type::Long,
                    Box::new(Instr::Extub(cond_gd.val.unwrap()))
                ));

                let cond_res_tmp = self.new_temp();
                let cmp_instr = Instr::Cmp(
                    Type::Long,
                    qbe::Cmp::Eq,
                    cond_val_tmp,
                    Value::Const(1)
                );
                self.fbuild.add_instr(Instr::Assign(
                    cond_res_tmp.clone(),
                Type::Long,
                    Box::new(cmp_instr)
                ));

                self.fbuild.add_instr(Instr::Jnz(
                        cond_res_tmp, 
                        body_lbl.clone(), // if true  
                        end.clone() // if false
                ));

                self.fbuild.add_block(body_lbl);

                let body_gd = self.gen_expr(body.node);
                if !body_gd.returned {
                    self.fbuild.add_instr(Instr::Jmp(loop_block));
                }

                self.fbuild.add_block(end);

                self.loop_exits.pop();
                self.loop_conts.pop();
            }
            AstNode::ForLoop { itervar, iter_upd, iter_cond, body } => {
                let _itervar_gd = self.gen_expr(itervar.node);

                let loop_block = self.alloc_label();
                let body_block = self.alloc_label();
                let end_block = self.alloc_label();

                self.loop_conts.push(loop_block.clone());
                self.loop_exits.push(end_block.clone());

                self.fbuild.add_instr(Instr::Jmp(loop_block.clone()));
                self.fbuild.add_block(loop_block.clone());

                let iter_cond_gd = self.gen_expr(iter_cond.node);

                self.fbuild.add_instr(Instr::Jnz(
                    iter_cond_gd.val.unwrap(),
                    body_block.clone(),
                    end_block .clone(),
                ));

                self.fbuild.add_block(body_block);
                let body_gd = self.gen_expr(body.node);
                let _iter_upd_gd = self.gen_expr(iter_upd.node);  
                if !body_gd.returned {
                    self.fbuild.add_instr(Instr::Jmp(loop_block));
                }

                self.fbuild.add_block(end_block);

                self.loop_exits.pop();
                self.loop_conts.pop();
            }
            AstNode::BreakLoop => {
                let exit = self.loop_exits.pop().unwrap();

                self.fbuild.add_instr(Instr::Jmp(exit));
                
                let blk_name = self.alloc_label();
                self.fbuild.add_block(blk_name); // making qbe stfu
            }
            AstNode::ContinueLoop => {
                let tgt = self.loop_conts.pop().unwrap();

                self.fbuild.add_instr(Instr::Jmp(tgt));
                
                let blk_name = self.alloc_label();
                self.fbuild.add_block(blk_name); // making qbe stfu
            }
            AstNode::ExternedFunc { name: _, args: _, ret_type: _, public: _, real_name: _ } => {

            }
            AstNode::Module { name , node } => {
                let old_mod = self.curmod.clone();
                self.curmod = match old_mod.as_str() {
                    "main" => name.clone(),
                    other => format!("{}::{}", other, name),
                };

                self.gen_expr(node.node);

                self.curmod = old_mod;
            }
            AstNode::Structure { name, fields: _, public: _, attrs } => {
                let name_st = name.path_to_string();
                let paths = self.get_use_paths();
                let struct_dat = self.struct_tab.get(&name_st, &paths)
                    .expect("Can't get struct info");

                let typedef = TypeDef {
                    name: name.path_to_segs().join("_"),
                    align: Some(struct_dat.max_alignment as u64),
                    items: struct_dat.fields.iter()
                        .map(|f| { 
                            let count = match &f.1.ftype {
                                FType::Array(el, ct) => *ct,
                                other => 1,
                            };
                            (
                                CodeGen::qtype_lose_sign(
                                    CodeGen::match_ft_qbf_t(&f.1.ftype, true)
                                ),
                                count,
                            )
                        })
                        .collect(),
                }; 
                self.module.add_type(typedef);
            }
            AstNode::StructCreate { name, field_vals } => {
                let name_st = name.path_to_string();
                
                let res_tmp = self.new_temp();
                let field_tmp = self.new_temp();
                let paths = self.get_use_paths();

                let struct_dat = self.struct_tab.get(&name_st, &paths)
                    .expect("Can't get struct info")
                    .clone();

                let alloc_instr = match struct_dat.max_alignment {
                    ..5 => Instr::Alloc4(struct_dat.size as u32),
                    5..9 => Instr::Alloc8(struct_dat.size as u64),
                    9.. => Instr::Alloc16(struct_dat.size as u128),
                };
                
                res.val = Some(res_tmp.clone());
                res.ftype = FType::Struct(
                    name_st
                );
                self.fbuild.assign_instr(
                    res_tmp.clone(),
                    Type::Long, // ptr 
                    alloc_instr
                ); 
                
                for (k, v) in field_vals {
                    let field_info = struct_dat.fields
                        .get(&k)
                        .unwrap();

                    self.fbuild.assign_instr(
                        field_tmp.clone(),
                        Type::Long,
                        Instr::Add(
                            res_tmp.clone(), 
                            Value::Const(field_info.offset as u64)
                        )
                    );   

                    let gd = self.gen_expr(*v);
                    match &field_info.ftype {
                        FType::Array(el, ct) if *ct != 0 => {
                            let tot_size = 
                                CodeGen::match_ft_qbf_t(&el, true).size() 
                                * (*ct as u64);
                            let args = vec![
                                (Type::Long, field_tmp.clone()), // dst 
                                (Type::Long, gd.val.unwrap()), // src 
                                (Type::Long, Value::Const(tot_size)), // len 
                            ];

                            self.fbuild.add_instr(Instr::Call(
                                "memcpy".into(),
                                args,
                                None
                            ));
                        }
                        FType::Struct(snm) => {
                            let tot_size = {
                                let paths = self.get_use_paths();
                                let struct_info = self.struct_tab.get(snm, &paths)
                                    .expect(&format!("Unknown struct {}", snm));
                                struct_info.size as u64
                            };

                            let args = vec![
                                (Type::Long, field_tmp.clone()), // dst 
                                (Type::Long, gd.val.unwrap()), // src 
                                (Type::Long, Value::Const(tot_size)), // len 
                            ];

                            self.fbuild.add_instr(Instr::Call(
                                "memcpy".into(),
                                args,
                                None
                            ));
                        }
                        other => {
                            // type dst val
                            self.fbuild.add_instr(Instr::Store(
                                CodeGen::match_ft_qbf_tl(&gd.ftype, true, true),
                                field_tmp.clone(),
                                gd.val.unwrap()
                            ));
                        }
                    } 
                }
            }
            AstNode::StructFieldAddr { val, field_name } => {
                res.by_addr = true;

                let gd = self.gen_expr(val.node);
                let tmp = self.new_temp();
                let paths = self.get_use_paths();
                
                let struct_name = match gd.ftype.if_struct() {
                    Some(s) => s.to_owned(),
                    None => panic!("Unexpected non-struct type {:?}", gd.ftype)
                };

                let struct_info = self.struct_tab.get(&struct_name, &paths)
                    .expect("Internal: can't get struct info");

                let field_info = struct_info.fields.get(&field_name)
                    .expect("Internal: can't get field info for struct");


                self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Add(
                        gd.val.clone().expect("Internal: expected value"),
                        Value::Const(field_info.offset as u64)
                    )
                );
                res.val = Some(tmp.clone());

                let holds_ptr = match &field_info.ftype {
                    FType::Array(el, ct) if *ct == 0 => true,
                    FType::Ptr | FType::TypePtr(_) | FType::StructPtr(_) | 
                        FType::StructHeapPtr(_) => true,
                    other => false
                };

                let is_emb = matches!(field_info.ftype, FType::Struct(_));

                if (!self.need_addr || (self.need_addr && holds_ptr))
                && !is_emb {
                    let load_tmp = self.new_temp();
                    res.val = Some(load_tmp.clone());

                    let field_qtype = Self::match_ft_qbf_t(&field_info.ftype, true);

                    self.fbuild.assign_instr(
                        load_tmp.clone(),
                        field_qtype.clone(),
                        Instr::Load(
                            field_qtype,
                            tmp.clone(),
                        )
                    );
                }
                res.ftype = field_info.ftype.clone();
            }
            AstNode::StructImpl { name, body, Trait } => {
                let _gd = self.gen_expr(body.node);
            }
            AstNode::MethodCall { name, args, idx } => {
                let first_arg = args.get(0).expect("Expected self");
                let cur_line = first_arg.line;

                let var_name = match &first_arg.node {
                    AstNode::Variable(s) => s.clone(),
                    other => unreachable!("{:?}", other)
                };

                let ft = self.symb_table
                    .get(&var_name)
                    .expect(&format!("Can't get symbol {}",
                            var_name));

                let self_ft = ft.1.ftype.clone();
                let struct_name = self_ft
                            .if_struct()
                            .expect(&format!("Expected struct, found {}",
                                    self_ft));

                let func_name = format!("{}::{}", struct_name, name.path_to_string());

                let mut res_args = Vec::new();
                let first = match self_ft {
                    FType::StructHeapPtr(st) => {
                        AstRoot::new(
                            AstNode::VariableCast { 
                                name: var_name, 
                                target_type: FType::StructPtr(st) 
                            },
                            cur_line
                        )
                    }
                    FType::Struct(st) => {
                        AstRoot::new(
                            AstNode::UnaryOp { 
                                op: UnaryOp::AddressOf, 
                                expr: Box::new(first_arg.node.clone())
                            },
                            cur_line
                        )
                    }
                    other => first_arg.clone()
                };
                res_args.push(first);
                res_args.extend_from_slice(&args[1..]);

                let call_node = AstNode::Call { 
                    func_name: Box::new(
                        AstNode::string_to_path(&func_name)
                    ), 
                    args: res_args, 
                    idx: idx 
                };

                res = self.gen_expr(call_node);
            }
            AstNode::Usemod { name } => {
                self.usedmods.push(name.path_to_string());
            }
            AstNode::Trait { name, body, public } => {

            }
            AstNode::none => {}
            other => {
                panic!("can't generate yet for {:#?}", other);
            }
        }
        if let Some(f) = self.fbuild.pop_func() {
            self.module.add_function(f);
        };
        if self.should_push {
            for (_idx, v) in res.instrs.drain(..).enumerate() {
                self.fbuild.add_instr(v);
            }
        }
        return res;
    }

    fn gen_func(&mut self, name: &AstNode, args: Vec<FuncArg>, 
            ret_type: FType, body: Box<AstNode>, over_idx: usize, public: bool)  {
        let mut res_args = args.clone();
        match &ret_type {
            FType::Struct(snm) => {
                let argdat = FuncArg::new(
                    "__hidden_sret".into(), 
                    FType::StructPtr(snm.clone())
                );
                res_args.insert(0, argdat);
            }
            other => {}
        }

        self.symb_table.push_funcargs(args.clone());
        self.fbuild.args_passed = res_args.clone();

        let mut args_qbe = Vec::new();
        for arg in &res_args {
            args_qbe.push((
                Self::match_ft_qbf_t(&arg.ftype, true),
                Value::Temporary(arg.name.to_owned())
            ));
        }

        let ret_t_qbe = match ret_type {
            FType::none | FType::nil => None,
            other => Some(Self::match_ft_qbf(&other))
        };

        let linkage = match public {
            true => Linkage::public(),
            false => Linkage::private(),
        };

        let mname = name.path_to_segs().join("_");
        let mut func = Function::new(
            linkage, 
            format!("{}_{}", mname, over_idx),
            args_qbe, 
            ret_t_qbe
        );
        func.add_block("start");
        self.fbuild.add_func(func, res_args.clone());
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
        self.fbuild.args_passed.clear();
    }

    /// Generates generic function and returns name of it 
    fn gen_generic_func(&mut self, fname: &str, args_ft: Vec<FType>, 
        ret_ft: &FType) -> String {

        let mut f_ast = self.genfuncs.get(fname)
            .expect(&format!("Internal: Expected generic function {}!", fname))
            .clone();

        let new_name = match &mut f_ast.node {
            AstNode::Function { name, args, ret_type, body, public } => {
                let generics = name.get_generics();
                let mut new_name_suf = name.path_to_string();
                for ft in args_ft.iter().take(generics.len()) {
                    let ft_name = FType::rm_prefix(&format!("{}", ft));

                    new_name_suf.push_str(&format!("::{}", ft_name));
                }
                let new_name_astn = AstNode::string_to_path(&new_name_suf);
                *name = Box::new(new_name_astn.clone());

                for (idx, new_ft) in args_ft.iter().enumerate() {
                    args[idx].ftype = new_ft.clone();
                }

                *ret_type = ret_ft.clone();

                new_name_astn.path_to_segs()
            }
            other => unreachable!("{}: Generic func expected, found {:?}", 
                f_ast.line, other)
        };

        let mut res = new_name.join("_");
        // don't generate if already did earlier 
        let already_generated = {
            let lock = self.prev_gen.read().unwrap();
            lock.contains(&res)
        };
        if !already_generated {
            self.deffered_gen.push(f_ast);
        }

        res.push_str("_0"); // overload 0 
        res
    }

    fn new_temp(&mut self) -> Value {
        let name = format!("tmp_{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        Value::Temporary(name)
    }

    fn new_dslab(&mut self) -> String {
        let name = format!("dsval_{}", self.dslbl_ctr);
        self.dslbl_ctr += 1;
        name
    }

    fn get_conv(ft_src: &FType, target_type: &FType, src: Value) -> Instr {
        match (ft_src, target_type) {
            (FType::StructPtr(st), FType::Ptr) | (FType::StructHeapPtr(st), 
                FType::Ptr) => {
                Instr::Copy(src)
            }
            (FType::double, FType::uint) => { // bitwise repr
                Instr::Dtoui(
                    src
                )
            }
            (FType::double, FType::int) => { // bitwise repr
                Instr::Dtosi(
                    src
                )
            }
            (FType::uint, FType::double) => {
                Instr::Ultof(
                    src
                )
            }
            (FType::int, FType::double) => {
                Instr::Sltof(
                    src
                )
            }
            (FType::int, FType::uint) | (FType::uint, FType::int) => {
                Instr::Copy(
                    src
                )
            }
            (FType::int, FType::bool) | (FType::uint, FType::bool) => {
                Instr::Cmp(
                    Type::Long,
                    qbe::Cmp::Ne,
                    src,
                    Value::Const(0)
                )
            }
            (FType::u32, FType::bool) | (FType::i32, FType::bool) => {
                Instr::Cmp(
                    Type::Word,
                    qbe::Cmp::Ne,
                    src,
                    Value::Const(0)
                )
            }
            (FType::u32, FType::uint) => {
                Instr::Extuw(src)
            }
            (FType::i32, FType::int) => {
                Instr::Extsw(src)
            }
            (FType::u32, FType::ubyte) => {
                Instr::And(src, Value::Const(255))
            }
            (FType::ubyte, FType::bool) | (FType::ibyte, FType::bool) => {
                Instr::Cmp(
                    Type::Byte,
                    qbe::Cmp::Ne,
                    src,
                    Value::Const(0)
                )
            }
            (FType::double, FType::single) => {
                Instr::Truncd(src)
            }
            (FType::single, FType::double) => {
                Instr::Exts(src)
            }
            (FType::single, other) | (other, FType::single) | (FType::double, other) |
                (other, FType::double) if ft_src.size() == target_type.size() => {
                Instr::Cast(src)
            }
            (FType::ishort, FType::i32) | (FType::ishort, FType::int) => {
                Instr::Extsh(src)
            }
            (FType::ushort, FType::u32) | (FType::ushort, FType::uint) => {
                Instr::Extuh(src)
            }
            (FType::ubyte, FType::uint) | (FType::ibyte, FType::uint) => {
                Instr::Extub(src)
            }
            (FType::ubyte, FType::int) | (FType::ibyte, FType::int) => {
                Instr::Extsb(src)
            }
            _other => unimplemented!("Type conv: {:?} => {:?}",
                ft_src, target_type)
        }
    }

    fn gen_cmp_op(&mut self, cmp_op: CmpOp, op1: GenData, op2: GenData)
            -> Value {
        let tmp = self.new_temp();
        let val1 = op1.val.unwrap();
        let val2 = op2.val.unwrap();

        if op1.ftype == FType::strconst {
            let func_tmp = self.new_temp();
            let args = vec![
                (Type::Long, val1.clone()), 
                (Type::Long, val2.clone())
            ];
            self.fbuild.assign_instr(
                func_tmp.clone(),
                Type::Word,
                Instr::Call("strcmp".into(), args, None) // libc
            ); 
            self.fbuild.assign_instr(
                tmp.clone(), 
                Type::Word,
                Instr::Cmp(
                    Type::Word,
                    qbe::Cmp::Eq,
                    func_tmp,
                    Value::Const(0)
                )
            );
            return tmp;
        }

        let is_unsigned = op1.ftype == FType::uint;

        let qbe_cmp = match cmp_op {
            CmpOp::Eq => qbe::Cmp::Eq,
            CmpOp::Ne => qbe::Cmp::Ne,

            CmpOp::G  => if is_unsigned { qbe::Cmp::Ugt } else { qbe::Cmp::Sgt },
            CmpOp::Ge => if is_unsigned { qbe::Cmp::Uge } else { qbe::Cmp::Sge },
            CmpOp::L  => if is_unsigned { qbe::Cmp::Ult } else { qbe::Cmp::Slt },
            CmpOp::Le => if is_unsigned { qbe::Cmp::Ule } else { qbe::Cmp::Sle },
        };

        let instr = Instr::Cmp(
            Self::match_ft_qbf(&op1.ftype),
            qbe_cmp,
            val1, val2
        );

        self.fbuild.assign_instr(
            tmp.clone(),
            Type::Word,
            instr
        );

        tmp
    }

    /// Calls destructors for dropped structs. Doesnt drop those passed as args
    fn leave_scope_clean(&mut self, dropped: &Vec<FSymbol>, except: Vec<Value>) {
        let mut full_except: Vec<Value> = self.fbuild.args_passed.iter().map(|a| {
            Value::Temporary(a.name.clone())
        }).collect();

        full_except.extend(except);

        for s in dropped {
            self.try_drop(s, &full_except);
        }
    }

    /// Attempts to drop value and returns whether it was actually dropped in result 
    fn try_drop(&mut self, s: &FSymbol, excepts: &Vec<Value>) -> bool {
        let paths = self.get_use_paths();
        if !s.owner {
            return false;
        }     
        if excepts.iter().any(|v| {v == &Value::Temporary(s.name.clone())}) {
            return false;
        }

        let mut args: Vec<(Type, Value)> = Vec::new();

        match &s.ftype {
            FType::Struct(st) | FType::StructPtr(st) => {
                let drop_funcname = format!("{}::drop::0", st);

                if self.func_tab.get_func(&drop_funcname, &paths).is_some() {
                    args.push((Type::Long, Value::Temporary(s.name.clone())));

                    self.fbuild.add_instr(Instr::Call(
                        drop_funcname.replace("::", "_"),
                        args.clone(),
                        None
                    ));
                }

                if let Some(si) = self.struct_tab.get(st, &paths) {
                    if si.attrs.contains(&fparse::Attr::Heap) {
                        args.push((Type::Long, Value::Temporary(s.name.clone())));

                        self.fbuild.add_instr(Instr::Call(
                            "free".to_owned(),
                            args,
                            None
                        ));
                    }
                }
                return true;
            }
            // heap ptr 
            other if other.if_struct().is_some() => {
                let st = other.if_struct().unwrap();
                let drop_funcname = format!("{}::drop", st);

                args.push((Type::Long, Value::Temporary(s.name.clone())));

                if self.func_tab.get_func(&drop_funcname, &paths).is_some() {
                    self.fbuild.add_instr(Instr::Call(
                        format!("{}_0", drop_funcname.replace("::", "_")),
                        args.clone(),
                        None
                    ));
                }

                self.fbuild.add_instr(Instr::Call(
                    "free".to_owned(),
                    args,
                    None
                ));
                return true;
            }
            other => {}
        }
        return false;
    }

    fn should_gen(&self, r: &AstRoot) -> bool {
        for attr in &r.attrs {
            match &attr {
                Attr::Target(tgts) => {
                    if !tgts.contains(&self.target) {
                        return false;
                    }
                }
                other => {}
            }
        }
        true
    }

    /// presaves idx but wont push into sbuf
    fn alloc_label(&mut self) -> String {
        let name = format!("label_{}", self.labels.len());
        self.labels.insert(name.clone(), self.sbuf.len());
        name
    }

    pub fn match_ft_qbf(ft: &FType) -> Type {
        Self::match_ft_qbf_t(ft, false) 
    }

    /// t - true conversion 
    /// l - lose sign 
    pub fn match_ft_qbf_tl(ft: &FType, t: bool, l: bool) -> Type { 
        let mut res = Self::match_ft_qbf_t(ft, t);
        if l {
            res = Self::qtype_lose_sign(res);
        }
        res
    }

    pub fn match_ft_qbf_t(ft: &FType, straight: bool) -> Type {
        match ft {
            FType::int | FType::uint  => Type::Long,
            FType::double             => Type::Double,
            FType::single             => Type::Single,
            FType::u32 | FType::i32   => Type::Word,
            FType::Array(el, _)    => {
                Self::match_ft_qbf(
                    &*el
                )
            },
            FType::strconst | FType::StructPtr(_)
                | FType::StructHeapPtr(_) | FType::Ptr => Type::Long, // ptr 
            FType::bool | FType::ubyte if straight 
                => Type::UnsignedByte,
            FType::ibyte if straight => Type::SignedByte,
            FType::bool | FType::ubyte | FType::ibyte => Type::Word,

            FType::ushort if straight => Type::UnsignedHalfword,
            FType::ishort if straight => Type::SignedHalfword,
            FType::ushort | FType::ishort => Type::Word,

            FType::Struct(s) if straight => Type::Aggregate(
                TypeDef { 
                    name: s.to_owned().replace("::", "_"), 
                    // other fields doesnt matter 
                    align: None, 
                    items: Vec::new()
                }
            ),
            FType::Struct(_s) => Type::Long,
            
            _other => todo!("Match ft qbf for {:?}", ft)
        }
    }

    pub fn qtype_lose_sign(qt: Type) -> Type {
        match qt {
            Type::SignedByte | Type::UnsignedByte => Type::Byte,
            Type::SignedHalfword | Type::UnsignedHalfword => Type::Halfword,
            other => other,
        }
    }

    pub fn sizeof(ft: &FType) -> u64 {
        match ft {
            FType::int | FType::uint | FType::double => 8,
            FType::bool => 4, // word type for bool asignments 
            _other => 8,
        }
    } 

    fn gen_stddat(&mut self) {
        let items = vec![
            (Type::Byte, DataItem::Str(r"%lu\n".into())),
            (Type::Byte, DataItem::Str(r"%ld\n".into())),
            (Type::Byte, DataItem::Str(r"%f\n".into())),
            (Type::Byte, DataItem::Str(r"%s\n".into()))
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
        self.module.add_data(DataDef::new(
            Linkage::private(),
            "fmt_str",
            None,
            items[3..4].to_vec()
        ));
    }

    fn gen_array_store(&mut self, el_type: &FType, idx_r: Option<AstRoot>, from: &Value,
        to: &Value) {
        let el_size = match &el_type {
            anyft if anyft.if_struct().is_some() => {
                let usemods = self.get_use_paths();
                let stnm = anyft.if_struct().unwrap();
                let struct_info = self.struct_tab.get(&stnm, &usemods)
                    .expect(&format!("Unknown struct type {}", stnm));
                struct_info.size as u64 
            },
            other => Self::sizeof(other)
        };

        if let Some(idx_rv) = idx_r {
            let el_idx_gd = self.gen_expr(idx_rv.node);

            let offset_tmp = self.new_temp();

            self.fbuild.assign_instr(
                offset_tmp.clone(),
                Type::Long,
                Instr::Mul(
                    Value::Const(el_size),
                    el_idx_gd.val.unwrap()
                )
            );

            self.fbuild.assign_instr(
                offset_tmp.clone(),
                Type::Long,
                Instr::Add(
                    offset_tmp.clone(),
                    from.clone()
                )
            );
        }

        if matches!(*el_type, FType::Struct(_)) {
            let args = vec![
                (Type::Long, to.clone()), // dst
                (Type::Long, from.clone()), // src 
                (Type::Long, Value::Const(el_size)) // size 
            ];

            self.fbuild.add_instr(Instr::Call(
                "memcpy".into(),
                args,
                None
            ));
        } else {
            self.fbuild.add_instr(
                Instr::Store(
                    Self::match_ft_qbf(&el_type),
                    to.clone(),
                    from.clone()
                ) 
            );
        }
    }

    fn allocalign(size: usize, max_al: usize) -> Instr {
        match max_al {
            ..5 => Instr::Alloc4(size as u32),
            5..9 => Instr::Alloc8(size as u64),
            9.. => Instr::Alloc16(size as u128)
        }
    }

    /// Return struct size and max alignment 
    fn get_struct_size(&mut self, name: &str) -> (usize, usize) {
        let paths = self.get_use_paths();
        let struct_info = self.struct_tab.get(name, &paths)
            .expect(&format!("Unknown struct {}", name));
        (struct_info.size, struct_info.max_alignment)
    }
    
    fn gen_intrinsic(&mut self, intrin: Intrinsic, rightdat: GenData) 
            -> GenData {
        let mut resd = GenData::new();
        match intrin {
            Intrinsic::Print => {
                let r_qtype = Self::match_ft_qbf_t(&rightdat.ftype, true);
                match r_qtype {
                    Type::Long => {
                        match rightdat.ftype {
                            FType::uint => {
                                let args = vec![
                                    (Type::Long, Value::Global("fmt_uint".into())),
                                    (Type::Long, rightdat.val.unwrap_or_else(|| {
                                        panic!("Internal error: expected args \
                                            for print")
                                    }))
                                ];

                                self.fbuild.add_instr(
                                    Instr::Call(
                                        "printf".into(),
                                        args, 
                                        None
                                    )
                                ); 
                            }
                            FType::int => {
                                let args = vec![
                                    (Type::Long, Value::Global("fmt_int".into())),
                                    (Type::Long, rightdat.val.unwrap_or_else(|| {
                                        panic!("Internal error: expected args \
                                            for print")
                                    }))
                                ];

                                self.fbuild.add_instr(
                                    Instr::Call(
                                        "printf".into(),
                                        args, 
                                        None
                                    )
                                );
                            }
                            FType::strconst => {
                                let args = vec![
                                        (Type::Long, Value::Global("fmt_str".into())),
                                        (Type::Long, rightdat.val.unwrap_or_else(|| {
                                            panic!("Internal error: expected args \
                                                for print")
                                        }))
                                    ];

                                    self.fbuild.add_instr(
                                        Instr::Call(
                                            "printf".into(),
                                            args, 
                                            None
                                        )
                                    );
                            }
                            other => unimplemented!("{:?}", other)
                        }
                    }
                    Type::Double | Type::Single => {
                        let args = vec![
                            (Type::Long, Value::Global("fmt_float".into())),
                            (r_qtype, rightdat.val.unwrap_or_else(|| {
                                panic!("Internal error: expected args \
                                        for print")
                            }))
                        ];
                        self.fbuild.add_instr(
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
                let tmp = self.new_temp();
                resd.val = Some(tmp.clone());
                resd.ftype = FType::uint;

                match rightdat.ftype {
                    FType::strconst => {
                        self.fbuild.assign_instr(
                            tmp,
                            Type::Long,
                            Instr::Call(
                                "strlen".into(), // libc
                                vec![(Type::Long, rightdat.val.unwrap())],
                                None,
                            )
                        );

                    }
                    FType::Array(_el, l) => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            Type::Long,
                            Instr::Copy(
                                Value::Const(l as u64)
                            )
                        );
                    }
                    other => unimplemented!("{:#?}", other)
                }
            }
            Intrinsic::Sizeof => {
                let tmp = self.new_temp();
                let s = match rightdat.ftype {
                    FType::Struct(st) => {
                        let paths = self.get_use_paths(); 
                        let struct_info = self.struct_tab.get(&st, &paths)
                            .expect(&format!(
                                    "Internal: can't get struct {}",
                                    st)
                            );
                        struct_info.size as u64 
                    }
                    ref _other => rightdat.ftype.size()
                };

                self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Copy(
                        Value::Const(s)
                    )
                );
                resd.val = Some(tmp);
                resd.ftype = FType::uint;
            }
            Intrinsic::Typeof => {
                resd.ftype = rightdat.ftype;
            }
            Intrinsic::BitsOf => {
                let tmp = self.new_temp();
                match rightdat.ftype {
                    FType::double => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            Type::Long,
                            Instr::Cast(rightdat.val.unwrap())
                        );
                        resd.ftype = FType::uint;
                    }
                    FType::single => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            Type::Word,
                            Instr::Cast(rightdat.val.unwrap())
                        );
                        resd.ftype = FType::u32;
                    }
                    other => panic!("Can't use _bits for type {}", other)
                }

                resd.val = Some(tmp);
            }
            Intrinsic::FromBits => {
                let tmp = self.new_temp();
                match rightdat.ftype {
                    FType::uint => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            Type::Double,
                            Instr::Cast(rightdat.val.unwrap())
                        );
                        resd.ftype = FType::double;
                    }
                    FType::u32 => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            Type::Single,
                            Instr::Cast(rightdat.val.unwrap())
                        );
                        resd.ftype = FType::single;
                    }
                    other => panic!("Can't use _frombits for type {}", other)
                }

                resd.val = Some(tmp);
            }
        }
        resd
    }
}

#[derive(Debug)] 
pub struct FuncBuilder {
    pub func: Option<Function>,
    pub ready: bool,
    pub args_passed: Vec<FuncArg>,
}

impl FuncBuilder {
    pub fn new() -> FuncBuilder {
        FuncBuilder { 
            func: None,
            ready: false,
            args_passed: Vec::new(),
        }
    }

    pub fn add_func(&mut self, f: Function, args: Vec<FuncArg>) {
        self.func = Some(f);
        self.args_passed = args;
    }

    pub fn add_instr(&mut self, i: Instr) {
        if let Some(f) = self.func.as_mut() {
            f.add_instr(i);
        } else {
            panic!("Can't get function in fbuild!");
        }
    }

    pub fn assign_instr(&mut self, dst: Value, t: Type, i: Instr) {
        if let Some(f) = self.func.as_mut() {
            f.assign_instr(dst, t, i);
        } else {
            panic!("Can't get current function in fbuild!")
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

    pub fn add_block<S>(&mut self, name: S) 
        where S: Into<String> {
        if let Some(f) = self.func.as_mut() {
            f.add_block(name);
        } else {
            panic!("Can't get current func in fbuild!")
        }
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

    pub returned: bool, // if expr has return 
    pub by_addr: bool,
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
            returned: false,
            by_addr: false,
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
