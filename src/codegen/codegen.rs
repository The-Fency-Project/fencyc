use std::{backtrace::Backtrace, collections::{HashMap, HashSet}, ptr::hash, sync::{Arc, Mutex, RwLock}};

use crate::{
    cli::{CompBackend, InputFlags, Target}, fcparse::fcparse::{self as fparse, AstRoot, Attr, BinaryOp, CmpOp, FuncArg, FuncTable, UnaryOp}, lexer::lexer::Intrinsic, mir::mir::{FBlock, FDataDef, FDataItem, FFunction, FFunctionKind, FInstr, FModule, FTerm, FTypeDef, FVal, FValue, IRBinOp, IRCmpOp, MIRTranslator}, seman::seman::{FSymbol, FType, OverloadTable, StructTable, SymbolTable, VarPosition}
}; // AstNode;
use fparse::AstNode;
use indexmap::IndexSet;

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
    pub module: FModule,
    pub fbuild: FuncBuilder,
    pub symb_table: SymbolTable,
    func_tab: Arc<FuncTable>,
    struct_tab: Arc<StructTable>,
    should_push: bool,
    tmp_ctr: usize,
    dslbl_ctr: usize,
    local_funcs: HashSet<String>,
    labels: HashMap<String, usize>, // usize for sbuf idx
    loop_exits: Vec<String>,
    loop_conts: Vec<String>,
    matched_overloads: OverloadTable, // call idx -> overload idx, ret type
    need_addr: bool,
    expected_type: FType,
    usedmods: Vec<String>,
    curmod: String,
    flags: Arc<InputFlags>,
    genfuncs: Arc<HashMap<String, AstRoot>>, // generic functions 
    deffered_gen: Vec<AstRoot>, // for generics mostly
    pub prev_gen: Arc<RwLock<IndexSet<String>>>, // which generic functions were already generated 
}

impl CodeGen {
    pub fn new(ast: Arc<Vec<AstRoot>>, mo: OverloadTable, 
        fnctb: Arc<FuncTable>, struct_tab: Arc<StructTable>, flags: Arc<InputFlags>,
        genfuncs: Arc<HashMap<String, AstRoot>>, prev_gen: Arc<RwLock<IndexSet<String>>>) 
        -> CodeGen {
        CodeGen {
            ast: ast,
            cur_ast: 0,
            sbuf: String::new(),
            module: FModule::new(),
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
            local_funcs: HashSet::new(),
            need_addr: false,
            expected_type: FType::none,
            usedmods: Vec::new(),
            curmod: "main".into(),
            flags: flags,
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
            if let AstNode::Function { name, ret_type, args, .. } = &node_cl {
                was_func = true;
                if (name.path_to_string() == "main::main") && (!had_main) && 
                    (!nomain) {
                    had_main = true;
                    self.gen_prologue(&args, ret_type.clone());
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
        self.finalize(); 
    }

    pub fn translate<T: MIRTranslator>(&self, backend: &mut T) 
    -> T::Output {
        backend.translate_module(&self.module)
    } 

    pub fn write_file(&self, fname: &str) -> Result<(), std::io::Error> {
        if let Some(parent) = std::path::Path::new(fname).parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(fname, &format!("{}", self.module))?;

        Ok(())
    }

    /// Generates prologue (main func)
    /// Check ret type first!
    fn gen_prologue(&mut self, args: &Vec<FuncArg>, ret_type: FType) {
        let main_args: Vec<(FValue, FType)> = args.iter()
            .map(|fa| (
                FValue::new(FVal::VarTmp(fa.name.clone()), fa.ftype.clone()),
                fa.ftype.clone()
            ))
            .collect();

        let f_ret_ty = match &ret_type {
            FType::none => FType::int,
            other => other.clone(),
        };

        let mut mainf = FFunction::new(
            "main".into(),
            true,
            main_args.clone(),
            f_ret_ty,
            FFunctionKind::Local,
        );

        let start_blk = FBlock::new("start".into());
        mainf.add_blk(start_blk);
        if ret_type != FType::none {
            let tmp = self.new_temp(&ret_type);
            mainf.assign_instr(
                tmp.clone(),
                ret_type,
                FInstr::Call("main_main_0".into(), main_args)
            );
            mainf.add_term(FTerm::Return(Some(tmp)));
        } else {
            mainf.add_instr(
                FInstr::Call("main_main_0".into(), main_args)
            );
            mainf.add_term(FTerm::Return(Some(
                FValue::new(
                    FVal::IConst(0),
                    FType::int
                )
            )));
        }

        self.local_funcs.insert(mainf.name.clone());
        self.module.add_func(mainf);
    }

    fn finalize(&mut self) {
        // for llvm: pre-declare imported/externed functions 
        match self.flags.backend.as_ref().unwrap() {
            CompBackend::LLVM => {
                for (fname, fdat) in self.func_tab.ft.iter() {
                    if self.local_funcs.contains(fname) {
                        continue;
                    }
                    for (idx, o) in fdat.iter().enumerate() {
                        let params = o.args 
                            .iter()
                            .map(|a| a.into_fmir())
                            .collect();
                        
                        let name = match o.real_name.as_ref() {
                            Some(v) => v.replace("::", "_"),
                            None => 
                                format!("{}_{}", fname.replace("::", "_"), idx)
                        };

                        let ff = FFunction { 
                            name,
                            public:  false,
                            params, 
                            ret_ft:  o.ret_type.clone(),
                            blocks:  Vec::new(),
                            kind:    FFunctionKind::Extern,
                            cur_blk: 0
                        };

                        self.module.add_func(ff);
                    }
                }
            }
            other => {}
        }
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
                    let to_val = FValue::new(FVal::VarTmp(to_ptr), FType::Ptr);

                    let args = vec![
                        (to_val.clone(), FType::Ptr), //dst 
                        (rightd.val.clone().unwrap(), FType::Ptr), // src 
                        (FValue::new(FVal::UConst(tot_size as u64), FType::uint),
                         FType::uint)
                    ];
                    
                    self.fbuild.add_instr(FInstr::Call(
                        "memcpy".into(),
                        args,
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

                self.fbuild.add_term(FTerm::Return(ret_val));
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

                let mut fargs = Vec::new();
                let mut args_ft = Vec::new(); // vec of args ftypes (for generics)

                match func_dat.ret_type {
                    FType::Struct(snm) => {
                        let (size, al) = self.get_struct_size(&snm);

                        let align = match al {
                            ..5 => 4,
                            5..9 => 8,
                            9.. => 16,
                        };

                        let stack_tmp = self.new_temp(&FType::Ptr);
                        self.fbuild.assign_instr(
                            stack_tmp.clone(),
                            FType::Ptr,
                            FInstr::Alloca(align, size as u64)
                        );

                        fargs.push((stack_tmp.clone(), FType::Ptr));
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

                    if matches!(gd.ftype, FType::Struct(_)) && gd.var.is_some() {
                        let var_name = gd.var.clone().unwrap();
                        if let Some(v) = self.symb_table.get_mut(&var_name) {
                            v.1.moved = Some(0);
                        };
                    }
                    
                    args_ft.push(gd.ftype.clone());

                    fargs.push((
                        gd.val.unwrap_or_else(|| {
                            panic!("args incomplete val")
                        }),
                        gd.ftype.clone()
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

                let instr = FInstr::Call(
                    name, 
                    fargs, 
                );
                let tmpvar = self.new_temp(&ret_type);

                res.val = Some(tmpvar.clone());
                res.ftype = ret_type.clone();
                
                if ret_type != FType::none {
                    self.fbuild.assign_instr(
                        tmpvar, 
                        ret_type, 
                        instr
                    );
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
                        {} assignment", name)
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
                    FValue::new(FVal::VarTmp(name), res_ft.clone()), 
                    res_ft.clone(), 
                    FInstr::Copy(res_ft.clone(), val)
                );
            }
            
            AstNode::Uint(uv) => {
                res.ftype = FType::uint;
                res.val = Some(FValue::new(FVal::UConst(uv), res.ftype.clone()));
            }

            AstNode::Int(iv) => {
                res.ftype = FType::int;
                res.val = Some(FValue::new(FVal::IConst(iv), res.ftype.clone()));
            }

            AstNode::Double(fv) => {
                res.ftype = FType::double;
                res.val = Some(FValue::new(FVal::DoubleConst(fv), res.ftype.clone()));
            }

            AstNode::Single(sv) => {
                res.ftype = FType::single;
                res.val = Some(FValue::new(FVal::SingleConst(sv), res.ftype.clone()));
            }

            AstNode::boolVal(bv) => {
                res.ftype = FType::bool;
                res.val = Some(FValue::new(FVal::UConst(bv as u64), res.ftype.clone()));
            }

            AstNode::I32(iwv) => {
                res.ftype = FType::i32;
                res.val = Some(FValue::new(FVal::IConst(iwv as i64), res.ftype.clone()));
            }

            AstNode::U32(uwv) => {
                res.ftype = FType::u32;
                res.val = Some(FValue::new(FVal::UConst(uwv as u64), res.ftype.clone()));
            }

            AstNode::Ishort(ihv) => {
                res.ftype = FType::ishort;
                res.val = Some(FValue::new(FVal::IConst(ihv as i64), res.ftype.clone()));
            }

            AstNode::Ushort(uhv) => {
                res.ftype = FType::ushort;
                res.val = Some(FValue::new(FVal::UConst(uhv as u64), res.ftype.clone()));
            }

            AstNode::Ibyte(ibv) => {
                res.ftype = FType::ibyte;
                res.val = Some(FValue::new(FVal::IConst(ibv as i64), res.ftype.clone()));
            }

            AstNode::Ubyte(ubv) => {
                res.ftype = FType::ubyte;
                res.val = Some(FValue::new(FVal::UConst(ubv as u64), res.ftype.clone()));
            }

            AstNode::StringLiteral(st) => {
                let st_name = self.new_dslab();
                let len = st.len();

                let items = vec![
                    (FDataItem::Str(st)  , FType::ubyte),
                    (FDataItem::Zeroes(1), FType::ubyte)
                ];

                self.module.add_datadef(FDataDef::new(
                    st_name.clone(), 
                    false, 
                    Some(8), 
                    items
                ));

                let mut symb = FSymbol::new(
                    st_name.clone(),
                    VarPosition::None, // obsolete 
                    FType::strconst
                );
                symb.len = Some(len);
                symb.dsname = Some(st_name.clone());
                self.symb_table.newsymb(symb);

                res.val = Some(FValue::new(FVal::VarGlb(st_name), FType::strconst));
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

                let tmp = self.new_temp(&FType::Ptr);

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

                let align = match el_size {
                    ..5 => 4,
                    5..9 => 8,
                    9.. => 16,
                };

                self.fbuild.assign_instr(
                    tmp.clone(),
                    FType::Ptr,
                    FInstr::Alloca(align, total_size)
                );

                let idx_tmp = self.new_temp(&FType::Ptr);
                for (i, v) in vals.iter().enumerate() { 
                    self.fbuild.assign_instr(
                        idx_tmp.clone(),
                        FType::Ptr,
                        FInstr::BinaryOp(
                            IRBinOp::Add,
                            tmp.clone(), 
                            FValue::new(FVal::UConst(i as u64 * el_size), FType::Usize)
                        )
                    );

                    if let Some(sn) = &agg {
                        // If dense array, rely on libc memcpy or copy if present 
                        let args = vec![
                            (idx_tmp.clone(), FType::Ptr),
                            (v.clone(), FType::Ptr),
                            (FValue::new(FVal::UConst(el_size), FType::uint),
                             FType::uint)
                        ];

                        self.fbuild.add_instr(
                            FInstr::Call(
                                "memcpy".into(),
                                args
                            )
                        );
                        // Original value will be dropped at the end of scope
                    } else {
                        self.fbuild.add_instr(FInstr::Store(
                            idx_tmp.clone(),
                            v.clone(),
                            ft.clone()
                        ));
                    }
                }

                res.val = Some(tmp);
            }
            AstNode::ArrayElem(arr, idx_val) => {
                let old_needaddr = self.need_addr;
                self.need_addr = true;
                let val_dat  = self.gen_expr(*arr);
                self.need_addr = false;

                let idx_gd   = self.gen_expr(idx_val.node);
                self.need_addr = old_needaddr;

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
                let tmp      = self.new_temp(&el_ftype);

                let el_size  = match &agg {
                    Some(v) => {
                        let paths = self.get_use_paths();
                        let dat = self.struct_tab.get(&v, &paths).unwrap();
                        dat.size as u64
                    } 
                    None => Self::sizeof(&el_ftype)
                };

                let offset = self.new_temp(&FType::Usize);

                self.fbuild.assign_instr(
                    offset.clone(),
                    FType::Usize,
                    FInstr::BinaryOp(
                        IRBinOp::Mul,
                        idx_gd.val.unwrap(),
                        FValue::new(FVal::UConst(el_size), FType::Usize)
                    )
                );

                let addr = self.new_temp(&FType::Ptr);

                self.fbuild.assign_instr(
                    addr.clone(),
                    FType::Ptr,
                    FInstr::GetAddr(
                        val_dat.val.unwrap().clone(),
                        offset.clone()
                    )
                );                
                res.by_addr = self.need_addr || agg.is_some();
                if !res.by_addr {
                    self.fbuild.assign_instr(
                        tmp.clone(),
                        el_ftype.clone(),
                        FInstr::Load(addr.clone(), el_ftype.clone())
                    );
                    res.val   = Some(tmp);
                } else {
                    res.val = Some(addr);
                }

                res.ftype = match agg {
                    Some(nm) => FType::StructPtr(nm),
                    None     => el_ftype
                };
            }
            AstNode::UnaryOp { op, expr } => {
                let mut gd = self.gen_expr(*expr);

                let tmp = self.new_temp(&gd.ftype);
                res.val = Some(tmp.clone());

                match op {
                    UnaryOp::Negate => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            gd.ftype.clone(),
                            FInstr::Neg(
                                gd.val.unwrap()
                            )
                        );
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::Not => {
                        self.fbuild.assign_instr(
                            tmp.clone(), 
                            gd.ftype.clone(), 
                            FInstr::BinaryOp(
                                IRBinOp::Xor,
                                gd.val.unwrap(), 
                                FValue::new(FVal::UConst(u64::MAX), gd.ftype.clone())
                            )
                        );
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::LogicalNot => {
                        self.fbuild.assign_instr(
                            tmp.clone(), 
                            gd.ftype.clone(), 
                            FInstr::Cmp(
                                IRCmpOp::Eq,
                                gd.ftype.clone(),
                                gd.val.unwrap(), 
                                FValue::new(FVal::UConst(0), gd.ftype.clone())
                            )
                        );
                        res.ftype = gd.ftype;
                    }
                    UnaryOp::AddressOf => {
                        // doesnt actually do anything since 
                        // struct is already a pointer
                        let res_tmp = self.new_temp(&FType::Ptr);

                        self.fbuild.assign_instr(
                            res_tmp.clone(),
                            FType::Ptr,
                            FInstr::GetAddr(
                                gd.val.clone().unwrap(), // base 
                                FValue::new(FVal::UConst(0), FType::Usize) // offset
                            )
                        ); 

                        res.ftype = match gd.ftype {
                            FType::Struct(s) => FType::StructPtr(s),
                            other => FType::TypePtr(Box::new(other.clone()))
                        };
                        res.val = Some(res_tmp);
                    }
                    UnaryOp::Deref => {
                        let ftype_exp = match &self.expected_type {
                            FType::none => match gd.ftype {
                                FType::StructPtr(s) | FType::StructHeapPtr(s) => 
                                    FType::Struct(s),
                                FType::TypePtr(t) => *t.clone(),
                                other => panic!("Deref of type {}", other)
                            },
                            other => other.clone(),
                        };
                        let (ftype_exp, instr) = match &ftype_exp {
                            other if other.if_struct().is_some() => {
                                let sn = other.if_struct().unwrap();
                                
                                (
                                    FType::Struct(sn),
                                    FInstr::Copy(FType::Ptr, gd.val.clone().unwrap())
                                )
                            },
                            other => (
                                other.clone(),
                                FInstr::Load(
                                    gd.val.clone().unwrap(),
                                    other.clone()
                                )
                            ), 
                        };

                        self.fbuild.assign_instr(
                            tmp.clone(),
                            ftype_exp.clone(),
                            instr 
                        );
                        res.ftype = ftype_exp;
                    }
                    other => todo!("unary op {:#?}", other)
                }
            }
            AstNode::BinaryOp { op, left, right } => {
                let old_needaddr = self.need_addr;
                self.need_addr = false;
                let leftd = self.gen_expr(*left);
                let rightd = self.gen_expr(*right);
                self.need_addr = old_needaddr;

                let tmp = self.new_temp(&leftd.ftype);

                let fbop = match op {
                    fparse::BinaryOp::Add => IRBinOp::Add,
                    fparse::BinaryOp::Substract => IRBinOp::Sub, 
                    fparse::BinaryOp::Multiply => IRBinOp::Mul, 
                    fparse::BinaryOp::Divide => IRBinOp::Div, 
                    fparse::BinaryOp::Remainder => IRBinOp::Rem, 
                    fparse::BinaryOp::Compare(cmp_op) => {
                        let val = self.gen_cmp_op(
                            cmp_op, 
                            leftd, 
                            rightd
                        );
                        res.val = Some(val);
                        res.ftype = FType::bool;
                        return res;
                    }
                    other => todo!("{:?}", other)
                };

                self.fbuild.assign_instr(
                    tmp.clone(),
                    leftd.ftype.clone(),
                    FInstr::BinaryOp(
                        fbop,
                        leftd.val.unwrap(),
                        rightd.val.unwrap(),
                    )
                );
                res.val = Some(tmp);
                res.ftype = leftd.ftype.clone();
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
                res.val = Some(FValue::new(FVal::VarTmp(var.clone()), res.ftype.clone()));
                res.var = Some(var.clone());
            }
            AstNode::VariableCast { name, target_type } => {
                res.ftype = target_type.clone();
                let symb  = self.symb_table.get(&name).unwrap();
                let og_ft = symb.1.ftype.clone();

                match (&og_ft, &target_type) {
                    (FType::Ptr, FType::StructPtr(_)) | (FType::Ptr, FType::Struct(_)) |
                        (FType::Ptr, FType::StructHeapPtr(_)) | 
                        (FType::StructHeapPtr(_), FType::StructPtr(_)) => {
                        let tmp = self.new_temp(&FType::Ptr);
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            FType::Ptr,
                            FInstr::Copy(
                                FType::Ptr,
                                FValue::new(FVal::VarTmp(name.clone()), FType::Ptr)
                            )
                        );
                        res.val = Some(tmp.clone());
                        return res;
                    }
                    _other => {}
                };

                let ft_src = symb.1.ftype.clone();

                let tmp = self.new_temp(&target_type);
                
                self.fbuild.assign_instr(
                    tmp.clone(),
                    target_type.clone(),
                    FInstr::Cast(
                        FValue::new(FVal::VarTmp(name.clone()), og_ft.clone()),
                        og_ft.clone(),
                        target_type.clone()
                    )
                );

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
                let tmp = self.new_temp(&target_type);

                self.fbuild.assign_instr(
                    tmp.clone(), 
                    target_type.clone(),
                    FInstr::Cast(
                        gd.val.unwrap(),
                        gd.ftype.clone(),
                        target_type.clone()
                    ) 
                );

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
                        self.fbuild.add_instr(FInstr::Store(
                            val.clone(),
                            gd.val.expect("Internal: can't get reas value"),
                            gd.ftype.clone()
                        ));
                    }
                    (_other, _) => {
                        self.fbuild.assign_instr(
                            val.clone(),
                            gd.ftype.clone(),
                            FInstr::Copy(
                                gd.ftype.clone(),
                                gd.val.unwrap_or_else(|| {
                                    panic!("Internal: can't get reas value")
                                })   
                            )
                        );
                    }
                }

                res.val = Some(val);
                res.ftype = gd.ftype;
            }
            AstNode::IfStatement { cond, if_true, if_false } => {
                let cond_gd = self.gen_expr(cond.node);

                let cond_val = cond_gd.val.clone().unwrap();

                let true_lab  = self.alloc_label();
                let false_lab = self.alloc_label();
                let endif     = self.alloc_label();

                let false_to = if if_false.is_some() {
                    false_lab.clone()
                } else {
                    endif.clone()
                };

                self.fbuild.add_term(FTerm::Branch { 
                    cond: cond_val.clone(), 
                    then_bl: true_lab.clone(), 
                    else_bl: false_to.clone(),
                });

                self.fbuild.add_block(true_lab);

                let true_gd = self.gen_expr(if_true.node);
                res.instrs.extend(true_gd.instrs);
                if !true_gd.returned { 
                    self.fbuild.add_term(FTerm::Jump(endif.clone()));
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

                self.fbuild.add_term(FTerm::Jump(loop_block.clone()));
                self.fbuild.add_block(loop_block.clone());
                
                let end     = self.alloc_label();
                self.loop_exits.push(end.clone());
                let body_lbl = self.alloc_label();

                let cond_gd = self.gen_expr(cond.node);

                let cond_val = cond_gd.val.clone().unwrap(); 

                self.fbuild.add_term(FTerm::Branch { 
                    cond: cond_val.clone(), 
                    then_bl: body_lbl.clone(), 
                    else_bl: end.clone() 
                });

                self.fbuild.add_block(body_lbl);

                let body_gd = self.gen_expr(body.node);
                if !body_gd.returned {
                    self.fbuild.add_term(FTerm::Jump(loop_block));
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

                self.fbuild.add_term(FTerm::Jump(loop_block.clone()));
                self.fbuild.add_block(loop_block.clone());

                let iter_cond_gd = self.gen_expr(iter_cond.node);

                self.fbuild.add_term(FTerm::Branch { 
                    cond: iter_cond_gd.val.unwrap(), 
                    then_bl: body_block.clone(), 
                    else_bl: end_block.clone() 
                });

                self.fbuild.add_block(body_block);
                let body_gd = self.gen_expr(body.node);
                let _iter_upd_gd = self.gen_expr(iter_upd.node);  
                if !body_gd.returned {
                    self.fbuild.add_term(FTerm::Jump(loop_block));
                }

                self.fbuild.add_block(end_block);

                self.loop_exits.pop();
                self.loop_conts.pop();
            }
            AstNode::BreakLoop => {
                let exit = self.loop_exits.pop().unwrap();

                self.fbuild.add_term(FTerm::Jump(exit));
                
                let blk_name = self.alloc_label();
                self.fbuild.add_block(blk_name); // making qbe stfu
            }
            AstNode::ContinueLoop => {
                let tgt = self.loop_conts.pop().unwrap();

                self.fbuild.add_term(FTerm::Jump(tgt));
                
                let blk_name = self.alloc_label();
                self.fbuild.add_block(blk_name); // making qbe stfu
            }
            AstNode::ExternedFunc { name, args, ret_type, public, real_name } => {
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

                let typedef = FTypeDef {
                    name: name.path_to_segs().join("_"),
                    align: Some(struct_dat.max_alignment as u64),
                    items: struct_dat.fields.iter()
                        .map(|f| { 
                            let count = match &f.1.ftype {
                                FType::Array(el, ct) => *ct,
                                other => 1,
                            };
                            (
                                f.1.ftype.clone(),
                                count,
                            )
                        })
                        .collect(),
                }; 
                self.module.add_typedef(typedef);
            }
            AstNode::StructCreate { name, field_vals } => {
                let name_st = name.path_to_string();
                
                let paths = self.get_use_paths();

                let struct_dat = self.struct_tab.get(&name_st, &paths)
                    .expect("Can't get struct info")
                    .clone();

                let align = match struct_dat.max_alignment {
                    ..5  => 4,
                    5..9 => 8,
                    9..  => 16,
                };

                let alloc_instr = FInstr::Alloca(align, struct_dat.size as u64);
               
                let res_tmp = self.new_temp(&FType::Ptr);
                res.val = Some(res_tmp.clone());
                res.ftype = FType::Struct(
                    name_st
                );

                self.fbuild.assign_instr(
                    res_tmp.clone(),
                    FType::Ptr, 
                    alloc_instr
                ); 
               
                let field_tmp = self.new_temp(&FType::Ptr);

                for (k, v) in field_vals {
                    let field_info = struct_dat.fields
                        .get(&k)
                        .unwrap();

                    self.fbuild.assign_instr(
                        field_tmp.clone(),
                        FType::Ptr,
                        FInstr::BinaryOp(
                            IRBinOp::Add,
                            res_tmp.clone(), 
                            FValue::new(
                                FVal::UConst(field_info.offset as u64),
                                FType::Usize
                            )
                        )
                    );   

                    let gd = self.gen_expr(*v);
                    match &field_info.ftype {
                        FType::Array(el, ct) if *ct != 0 => {
                            let tot_size = 
                                el.size(Some(self.flags.target))
                                * (*ct as u64);
                            let args = vec![
                                (field_tmp.clone(), FType::Ptr), // dst 
                                (gd.val.unwrap(), FType::Ptr), // src 
                                (FValue::new(
                                    FVal::UConst(tot_size),
                                    FType::Usize
                                ), FType::Usize), // len 
                            ];

                            self.fbuild.add_instr(FInstr::Call(
                                "memcpy".into(),
                                args,
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
                                (field_tmp.clone(), FType::Ptr), // dst 
                                (gd.val.unwrap(), FType::Ptr), // src 
                                (FValue::new(
                                    FVal::UConst(tot_size),
                                    FType::Usize
                                ),
                                FType::Usize), // len 
                            ];

                            self.fbuild.add_instr(FInstr::Call(
                                "memcpy".into(),
                                args,
                            ));
                        }
                        other => {
                            self.fbuild.add_instr(FInstr::Store(
                                field_tmp.clone(),
                                gd.val.unwrap(),
                                gd.ftype, 
                            ));
                        }
                    } 
                }
            }
            AstNode::StructFieldAddr { val, field_name } => {
                res.by_addr = true;

                let gd = self.gen_expr(val.node);
                let tmp = self.new_temp(&FType::Ptr);
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
                    FType::Ptr,
                    FInstr::BinaryOp(
                        IRBinOp::Add,
                        gd.val.clone().expect("Internal: expected value"),
                        FValue::new(
                            FVal::UConst(field_info.offset as u64),
                            FType::Usize,
                        )
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
                    let load_tmp = self.new_temp(&field_info.ftype);
                    res.val = Some(load_tmp.clone());

                    self.fbuild.assign_instr(
                        load_tmp.clone(),
                        field_info.ftype.clone(),
                        FInstr::Load(
                            tmp.clone(),
                            field_info.ftype.clone(),
                        )
                    );
                    res.by_addr = self.need_addr;
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
            self.local_funcs.insert(f.name.clone());
            self.module.add_func(f);
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

        let mut args_mir = Vec::new();
        for arg in &res_args {
            args_mir.push((
                FValue::new(FVal::VarTmp(arg.name.to_owned()), arg.ftype.clone()),
                arg.ftype.clone()
            ));
        }

        let mname = name.path_to_segs().join("_");
        let mut func = FFunction::new(
            format!("{}_{}", mname, over_idx),
            public,
            args_mir, 
            ret_type.clone(),
            FFunctionKind::Local
        );

        let start_blk = FBlock::new("start".into());
        func.add_blk(start_blk);

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

    fn new_temp(&mut self, ft: &FType) -> FValue {
        let name = format!("tmp_{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        FValue::new(FVal::VarTmp(name), ft.clone())
    }

    fn new_dslab(&mut self) -> String {
        let name = format!("dsval_{}", self.dslbl_ctr);
        self.dslbl_ctr += 1;
        name
    }

    fn gen_cmp_op(&mut self, cmp_op: CmpOp, op1: GenData, op2: GenData)
            -> FValue {
        let val1 = op1.val.unwrap();
        let val2 = op2.val.unwrap();

        if op1.ftype == FType::strconst {
            let func_tmp = self.new_temp(&FType::u32);
            let args = vec![
                (val1.clone(), FType::Ptr), 
                (val2.clone(), FType::Ptr)
            ];
            self.fbuild.assign_instr(
                func_tmp.clone(),
                FType::u32,
                FInstr::Call("strcmp".into(), args) // libc
            ); 

            let tmp  = self.new_temp(&FType::u32);
            self.fbuild.assign_instr(
                tmp.clone(), 
                FType::u32,
                FInstr::Cmp(
                    IRCmpOp::Eq,
                    FType::ubyte,
                    func_tmp,
                    FValue::new(FVal::UConst(0), FType::bool)
                )
            );
            return tmp;
        }

        let mir_cmp = match cmp_op {
            CmpOp::Eq => IRCmpOp::Eq,
            CmpOp::Ne => IRCmpOp::Ne,

            CmpOp::G  => IRCmpOp::Gt,
            CmpOp::Ge => IRCmpOp::Ge,
            CmpOp::L  => IRCmpOp::Lt,
            CmpOp::Le => IRCmpOp::Le,
        };

        let instr = FInstr::Cmp(
            mir_cmp,
            op1.ftype,
            val1, 
            val2
        );

        let tmp = self.new_temp(&FType::bool);
        self.fbuild.assign_instr(
            tmp.clone(),
            FType::bool,
            instr
        );

        tmp
    }

    /// Calls destructors for dropped structs. Doesnt drop those passed as args
    fn leave_scope_clean(&mut self, dropped: &Vec<FSymbol>, except: Vec<FValue>) {

        let mut full_except: Vec<FValue> = self.fbuild.args_passed.iter().map(|a| {
            FValue::new(FVal::VarTmp(a.name.clone()), a.ftype.clone())
        }).collect();

        full_except.extend(except);

        for s in dropped {
            self.try_drop(s, &full_except);
        }
    }

    /// Attempts to drop value and returns whether it was actually dropped in result 
    fn try_drop(&mut self, s: &FSymbol, excepts: &Vec<FValue>) -> bool {
        let paths = self.get_use_paths();
        if !s.owner || s.moved.is_some() {
            return false;
        }     
        if excepts.iter().any(|v| {
            *v == FValue::new(FVal::VarTmp(s.name.clone()), s.ftype.clone())
        }) {
            return false;
        }

        let mut args: Vec<(FValue, FType)> = Vec::new();

        match &s.ftype {
            FType::Struct(st) | FType::StructPtr(st) => {
                let drop_funcname = format!("{}::drop", st);

                if self.func_tab.get_func(&drop_funcname, &paths).is_some() {
                    args.push((
                        FValue::new(FVal::VarTmp(s.name.clone()), FType::Ptr), 
                        FType::Ptr 
                    ));

                    self.fbuild.add_instr(FInstr::Call(
                        format!("{}_0", drop_funcname.replace("::", "_")),
                        args.clone(),
                    ));
                }

                if let Some(si) = self.struct_tab.get(st, &paths) {
                    if si.attrs.contains(&fparse::Attr::Heap) {
                        args.push((
                            FValue::new(FVal::VarTmp(s.name.clone()), FType::Ptr),
                            FType::Ptr
                        ));

                        self.fbuild.add_instr(FInstr::Call(
                            "free".to_owned(),
                            args,
                        ));
                    }
                }
                return true;
            }
            // heap ptr 
            other if other.if_struct().is_some() => {
                let st = other.if_struct().unwrap();
                let drop_funcname = format!("{}::drop", st);

                args.push((
                    FValue::new(FVal::VarTmp(s.name.clone()), FType::Ptr),
                    FType::Ptr
                ));

                if self.func_tab.get_func(&drop_funcname, &paths).is_some() {
                    self.fbuild.add_instr(FInstr::Call(
                        format!("{}_0", drop_funcname.replace("::", "_")),
                        args.clone(),
                    ));
                }

                self.fbuild.add_instr(FInstr::Call(
                    "free".to_owned(),
                    args,
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
                    if !tgts.contains(&self.flags.target) {
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

    pub fn sizeof(ft: &FType) -> u64 {
        match ft {
            FType::int | FType::uint | FType::double => 8,
            FType::bool => 4, // word type for bool asignments 
            _other => 8,
        }
    } 

    fn gen_stddat(&mut self) {
        let items = match self.flags.backend.as_ref().unwrap() {
            CompBackend::QBE => vec![
                (FDataItem::Str(r"%lu\n".into()), FType::ubyte),
                (FDataItem::Str(r"%ld\n".into()), FType::ubyte),
                (FDataItem::Str(r"%f\n".into()) , FType::ubyte),
                (FDataItem::Str(r"%s\n".into()) , FType::ubyte)
            ], 
            CompBackend::LLVM => vec![
                (FDataItem::Str("%lu\n".into()), FType::ubyte),
                (FDataItem::Str("%ld\n".into()), FType::ubyte),
                (FDataItem::Str("%f\n".into()) , FType::ubyte),
                (FDataItem::Str("%s\n".into()) , FType::ubyte)
            ],
        };

        self.module.add_datadef(FDataDef::new(
            "fmt_uint".into(),
            false,
            None,
            items[0..1].to_vec()
        ));
        self.module.add_datadef(FDataDef::new(
            "fmt_int".into(),
            false,
            None,
            items[1..2].to_vec()
        ));
        self.module.add_datadef(FDataDef::new(
            "fmt_float".into(),
            false,
            None,
            items[2..3].to_vec()
        ));
        self.module.add_datadef(FDataDef::new(
            "fmt_str".into(),
            false,
            None,
            items[3..4].to_vec()
        ));
    }

    fn gen_array_store(&mut self, el_type: &FType, idx_r: Option<AstRoot>, from: &FValue,
        to: &FValue) {
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

            let offset_tmp = self.new_temp(&FType::Ptr);

            self.fbuild.assign_instr(
                offset_tmp.clone(),
                FType::Ptr,
                FInstr::BinaryOp(
                    IRBinOp::Mul,
                    FValue::new(FVal::UConst(el_size), FType::Usize),
                    el_idx_gd.val.unwrap()
                )
            );

            self.fbuild.assign_instr(
                offset_tmp.clone(),
                FType::Ptr,
                FInstr::BinaryOp(
                    IRBinOp::Add,
                    offset_tmp.clone(),
                    from.clone()
                )
            );
        }

        if matches!(*el_type, FType::Struct(_)) {
            let args = vec![
                (to.clone(), FType::Ptr), // dst
                (from.clone(), FType::Ptr), // src 
                (FValue::new(
                    FVal::UConst(el_size),
                    FType::Usize
                ), FType::Usize) // size 
            ];

            self.fbuild.add_instr(FInstr::Call(
                "memcpy".into(),
                args,
            ));
        } else {
            self.fbuild.add_instr(
                FInstr::Store(
                    to.clone(),
                    from.clone(),
                    el_type.clone()
                ) 
            );
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
                match &rightdat.ftype {
                    FType::uint => {
                        let args = vec![
                            (
                                FValue::new(FVal::VarGlb("fmt_uint".into()), FType::Ptr),
                                FType::Ptr,
                            ),
                            (rightdat.val.unwrap_or_else(|| {
                                panic!("Internal error: expected args \
                                    for print")
                            }), FType::uint),
                        ];

                        self.fbuild.add_instr(
                            FInstr::Call(
                                "printf".into(),
                                args, 
                            )
                        ); 
                    }
                    FType::int => {
                        let args = vec![
                            (
                                FValue::new(FVal::VarGlb("fmt_int".into()), FType::Ptr),
                                FType::Ptr,
                            ),
                            (rightdat.val.unwrap_or_else(|| {
                                panic!("Internal error: expected args \
                                    for print")
                            }), FType::int),
                        ];

                        self.fbuild.add_instr(
                            FInstr::Call(
                                "printf".into(),
                                args, 
                            )
                        );
                    }
                    FType::strconst => {
                        let args = vec![
                            (
                                FValue::new(FVal::VarGlb("fmt_str".into()), FType::Ptr),
                                FType::Ptr,
                            ),
                            (rightdat.val.unwrap_or_else(|| {
                                panic!("Internal error: expected args \
                                    for print")
                            }), FType::strconst),
                        ];

                        self.fbuild.add_instr(
                            FInstr::Call(
                                "printf".into(),
                                args, 
                            )
                        );
                    }
                    FType::double | FType::single => {
                        let args = vec![
                            (
                                FValue::new(FVal::VarGlb("fmt_float".into()), FType::Ptr),
                                FType::Ptr,
                            ),
                            (rightdat.val.unwrap_or_else(|| {
                                panic!("Internal error: expected args \
                                    for print")
                            }), rightdat.ftype.clone()),
                        ];

                        self.fbuild.add_instr(
                            FInstr::Call(
                                "printf".into(),
                                args, 
                            )
                        );
                    }

                    other => todo!("Print for {:?}", other)
                }
            }
            Intrinsic::Len => {
                let tmp = self.new_temp(&FType::uint);
                resd.val = Some(tmp.clone());
                resd.ftype = FType::uint;

                match rightdat.ftype {
                    FType::strconst => {
                        self.fbuild.assign_instr(
                            tmp,
                            FType::uint,
                            FInstr::Call(
                                "strlen".into(), // libc
                                vec![(rightdat.val.unwrap(), FType::Ptr)],
                            )
                        );

                    }
                    FType::Array(_el, l) => {
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            FType::uint,
                            FInstr::Copy(
                                FType::uint,
                                FValue::new(
                                    FVal::UConst(l as u64),
                                    FType::uint
                                )
                            )
                        );
                    }
                    other => unimplemented!("{:#?}", other)
                }
            }
            Intrinsic::Sizeof => {
                let tmp = self.new_temp(&FType::uint);
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
                    ref _other => rightdat.ftype.size(Some(self.flags.target))
                };

                self.fbuild.assign_instr(
                    tmp.clone(),
                    FType::uint,
                    FInstr::Copy(
                        FType::uint,
                        FValue::new(FVal::UConst(s), FType::uint)
                    )
                );
                resd.val = Some(tmp);
                resd.ftype = FType::uint;
            }
            Intrinsic::Typeof => {
                resd.ftype = rightdat.ftype;
            }
            Intrinsic::BitsOf => {
                match rightdat.ftype {
                    FType::double => {
                        let tmp = self.new_temp(&FType::uint);
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            FType::uint,
                            FInstr::ReinterpretBits(
                                rightdat.val.unwrap(),
                                rightdat.ftype.clone(),
                                FType::uint
                            )
                        );
                        resd.val = Some(tmp);
                        resd.ftype = FType::uint;
                    }
                    FType::single => {
                        let tmp = self.new_temp(&FType::u32);
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            FType::u32,
                            FInstr::ReinterpretBits(
                                rightdat.val.unwrap(),
                                rightdat.ftype.clone(),
                                FType::u32
                            )
                        );
                        resd.val = Some(tmp);
                        resd.ftype = FType::u32;
                    }
                    other => panic!("Can't use _bits for type {}", other)
                }

            }
            Intrinsic::FromBits => {
                match rightdat.ftype {
                    FType::uint => {
                        let tmp = self.new_temp(&FType::double);
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            FType::double,
                            FInstr::ReinterpretBits(
                                rightdat.val.unwrap(),
                                rightdat.ftype.clone(),
                                FType::double,
                            )
                        );
                        resd.ftype = FType::double;
                        resd.val = Some(tmp);
                    }
                    FType::u32 => {
                        let tmp = self.new_temp(&FType::single);
                        self.fbuild.assign_instr(
                            tmp.clone(),
                            FType::single,
                            FInstr::ReinterpretBits(
                                rightdat.val.unwrap(),
                                rightdat.ftype.clone(),
                                FType::single
                            )
                        );
                        resd.ftype = FType::single;
                        resd.val = Some(tmp);
                    }
                    other => panic!("Can't use _frombits for type {}", other)
                }

            }
        }
        resd
    }
}

#[derive(Debug)] 
pub struct FuncBuilder {
    pub func: Option<FFunction>,
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

    pub fn add_func(&mut self, f: FFunction, args: Vec<FuncArg>) {
        self.func = Some(f);
        self.args_passed = args;
    }

    pub fn add_instr(&mut self, i: FInstr) {
        if let Some(f) = self.func.as_mut() {
            f.add_instr(i);
        } else {
            panic!("Can't get function in fbuild!");
        }
    }

    pub fn assign_instr(&mut self, dst: FValue, t: FType, i: FInstr) {
        if let Some(f) = self.func.as_mut() {
            f.assign_instr(dst, t, i);
        } else {
            panic!("Can't get current function in fbuild!")
        }
    }

    pub fn pop_func(&mut self) -> Option<FFunction> {
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
            let blk = FBlock::new(name.into());
            let id = f.add_blk(blk);
            f.set_cur_blkid(id);
        } else {
            panic!("Can't get current func in fbuild!")
        }
    }

    pub fn add_term(&mut self, term: FTerm) {
        if let Some(f) = self.func.as_mut() {
            f.add_term(term);
        } else {
            panic!("Can't get current func in fbuild!")
        }
    }
}

/// code generation data for each generated expression
#[derive(Debug, Clone)]
pub struct GenData {
    pub var: Option<String>,
    pub ftype: FType,

    pub val: Option<FValue>,
    pub qtype: Option<FType>,
   
    pub instrs: Vec<FInstr>,

    pub returned: bool, // if expr has return 
    pub by_addr: bool,
}

impl GenData {
    pub fn new() -> GenData {
        GenData {
            var: None,
            ftype: FType::none,
            instrs: Vec::new(),
            val: None,
            qtype: None,
            returned: false,
            by_addr: false,
        }
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
