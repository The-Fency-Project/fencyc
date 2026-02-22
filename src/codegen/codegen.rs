use std::{collections::HashMap, fmt::format, rc::Rc};

use crate::{
    fcparse::fcparse::{self as fparse, AstRoot, BinaryOp, CmpOp, FuncArg, UnaryOp},
    lexer::lexer::Intrinsic,
    seman::seman::{self as sem, FSymbol, FType, OverloadTable, SemAn, SymbolTable, VarPosition, idx_to_ftype},
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
    dslbl_ctr: usize,
    funcs: HashMap<String, FuncData>,
    labels: HashMap<String, usize>, // usize for sbuf idx
    loop_exits: Vec<String>,
    loop_conts: Vec<String>,
    stackidxs: Vec<usize>, // saving last stack idx before function
    matched_overloads: OverloadTable, // call idx -> overload idx, ret type
}

impl CodeGen {
    pub fn new(ast: Vec<AstRoot>, mo: OverloadTable) -> CodeGen {
        CodeGen {
            ast: ast,
            cur_ast: 0,
            sbuf: String::new(),
            module: Module::new(),
            fbuild: FuncBuilder::new(),
            should_push: true,
            symb_table: SymbolTable::new(),
            tmp_ctr: 0,
            dslbl_ctr: 0,
            labels: HashMap::new(),
            loop_exits: Vec::new(),
            loop_conts: Vec::new(),
            stackidxs: Vec::new(),
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
                self.gen_func(name, args, ret_type, body, 0); 
            }
            AstNode::FunctionOverload { func, idx } => {
                let (name, args, ret_type, body) = match *func {
                    AstNode::Function { name, args, ret_type, body } => {
                        (name, args, ret_type, body)
                    }
                    other => unreachable!()
                };

                self.gen_func(name, args, ret_type, body, idx); 
            }
            AstNode::ReturnVal { val } => {
                let rightd = self.gen_expr(val.node);
                res.returned = true;

                self.fbuild.add_instr(Instr::Ret(rightd.val));
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

                let name = match ov_idx {
                    Some(v) => format!("{}_{}", func_name, v),
                    None => format!("{}", func_name)
                };

                let instr = Instr::Call(
                        name, 
                        args_qbe, 
                        None
                );
                let tmpvar = self.new_temp();

                res.val = Some(tmpvar.clone());
                res.ftype = ret_type;
                
                if ret_type != FType::none {
                    self.fbuild.add_instr(Instr::Assign(
                        tmpvar, 
                        Self::match_ft_qbf(ret_type), 
                        Box::new(instr)
                    ));
                } else {
                    self.fbuild.add_instr(instr);
                }
            }
            AstNode::CodeBlock { exprs } => {
                self.symb_table.enter_scope();
                for expr in exprs {
                    let gend = self.gen_expr(expr.node);
                    res.instrs.extend(gend.instrs);
                    res.returned = gend.returned;
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

                self.fbuild.add_instr(
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
            AstNode::boolVal(bv) => {
                let val = Value::Const(bv as u64);
                res.val = Some(val);
                res.ftype = FType::bool;
            }
            AstNode::StringLiteral(st) => {
                let st_name = self.new_dslab();

                let items = vec![
                    (Type::Byte, DataItem::Str(st)),
                    (Type::Byte, DataItem::Const(0))
                ];

                self.module.add_data(DataDef { 
                    linkage: Linkage::private(), // TODO: pub
                    name: st_name.clone(), 
                    align: Some(8), 
                    items: items
                });

                self.symb_table.newsymb(FSymbol::new(
                    st_name.clone(),
                    VarPosition::None, // obsolete 
                    FType::strconst
                ));

                res.val = Some(Value::Global(st_name));
                res.ftype = FType::strconst;
            }
            AstNode::Array(ft, elems) => {
                let tmp = self.new_temp();

                let mut total_size: u64 = 0;
                let mut el_size: u64    = 0;
                let mut vals = Vec::new();
                for el in elems {
                    let gd = self.gen_expr(el);
                    vals.push(gd.val.clone().unwrap());
                    if el_size == 0 {
                        el_size = Self::sizeof(gd.ftype);
                    }
                    total_size += el_size;
                }

                let _ = self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Alloc8(total_size)
                );

                let qtype = Self::match_ft_qbf(ft);
                let idx_tmp = self.new_temp();
                for (i, v) in vals.iter().enumerate() { 
                    let _ = self.fbuild.assign_instr(
                        idx_tmp.clone(),
                        Type::Long,
                        Instr::Add(
                            tmp.clone(), 
                            Value::Const(i as u64 * el_size)
                        )
                    );

                    let _ = self.fbuild.add_instr(Instr::Store(
                        qtype.clone(),
                        idx_tmp.clone(),
                        v.clone()
                    ));
                }

                res.val = Some(tmp);
            }
            AstNode::ArrayElem(arr_name, idx_val) => {
                let idx_gd   = self.gen_expr(idx_val.node);
                let tmp = self.new_temp();
                let symb     = self.symb_table.get(arr_name.clone()).unwrap();

                let el_ftype = match symb.1.ftype {
                    FType::Array(el, _, _) => {
                        idx_to_ftype(el).unwrap()
                    }
                    other => unreachable!()
                };

                let el_size  = Self::sizeof(el_ftype);
                let el_qtype = Self::match_ft_qbf(el_ftype);

                let _ = self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Mul(idx_gd.val.unwrap(), Value::Const(el_size))
                );
               
                let _ = self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Add(tmp.clone(), Value::Temporary(arr_name.clone()))
                );

                let _ = self.fbuild.assign_instr(
                    tmp.clone(),
                    Type::Long,
                    Instr::Load(el_qtype, tmp.clone())
                );

                res.val   = Some(tmp);
                res.ftype = el_ftype;
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
                        self.fbuild.add_instr(Instr::Assign(
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
                        self.fbuild.add_instr(Instr::Assign(
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
                        self.fbuild.add_instr(Instr::Assign(
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
                let mut rightd = self.gen_expr(*right);

                let tmp = self.new_temp();

                match op {
                    fparse::BinaryOp::Add => {
                        self.fbuild.add_instr(Instr::Assign(
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
                        self.fbuild.add_instr(Instr::Assign(
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
                        self.fbuild.add_instr(Instr::Assign(
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
                        self.fbuild.add_instr(Instr::Assign(
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
                        self.fbuild.add_instr(Instr::Assign(
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
                let gend = self.gen_expr(*val);
                
                let mut ind = self.gen_intrinsic(intr, gend);
                for instr in ind.instrs.drain(..) {
                    self.fbuild.add_instr(instr);
                }
            }
            AstNode::Variable(var) => { // var name
                let var_dat = self.symb_table.get(var.clone()).unwrap_or_else(|| {
                    panic!("Internal: Can't get variable {}", var)
                });

                res.ftype = var_dat.1.ftype;
                res.qtype = Some(Self::match_ft_qbf(var_dat.1.ftype));
                res.val = Some(Value::Temporary(var.clone()));
            }
            AstNode::VariableCast { name, target_type } => {
                let symb = self.symb_table.get(name.clone()).unwrap();

                let ft_src = symb.1.ftype;
                let tmp = self.new_temp();
                
                let conv_instr = Self::get_conv(
                    ft_src, 
                    target_type, 
                    Value::Temporary(name.clone())
                );

                // QBE doesnt like byte assignments
                let tgt_qtype = match Self::match_ft_qbf(target_type) {
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
                let mut gd = self.gen_expr(*expr);
                res.instrs.extend(gd.instrs.extract_if(.., |x| {
                    matches!(x, Instr::Assign(_, _, _))
                }));
                let tmp = self.new_temp();

                let conv = Self::get_conv(
                        gd.ftype, 
                        target_type, 
                        gd.val.unwrap()
                );
                
                let tgt_qtype = match Self::match_ft_qbf(target_type) {
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
            AstNode::Reassignment { name, newval } => {
                let mut gd = self.gen_expr(newval.node);
                res.instrs.extend(gd.instrs.extract_if(.., |x| {
                    matches!(x, Instr::Assign(_, _, _))
                }));

                let val = Value::Temporary(name.clone());

                self.fbuild.add_instr(Instr::Assign(
                    val.clone(),
                    Self::match_ft_qbf(gd.ftype), 
                    Box::new(Instr::Copy(gd.val.unwrap_or_else(|| {
                        panic!("Internal: can't get reas value")
                    })))
                ));

                res.val = Some(val);
                res.ftype = gd.ftype;
            }
            AstNode::IfStatement { cond, if_true, if_false } => {
                let cond_gd = self.gen_expr(cond.node);

                let cond_val_tmp = self.new_temp();
                let _ = self.fbuild.add_instr(Instr::Assign(
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
                let _ = self.fbuild.add_instr(Instr::Assign(
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

                let _ = self.fbuild.add_instr(Instr::Jnz(
                        cond_res_tmp, 
                        true_lab.clone(), // if true  
                        false_to // if false
                ));

                let _ = self.fbuild.add_block(true_lab);

                let true_gd = self.gen_expr(if_true.node);
                res.instrs.extend(true_gd.instrs);
                if !true_gd.returned { 
                    let _ = self.fbuild.add_instr(Instr::Jmp(endif.clone()));
                }

                if let Some(n) = if_false {
                    let _ = self.fbuild.add_block(false_lab);
                    let false_gd = self.gen_expr(n.node);
                    res.instrs.extend(false_gd.instrs);
                }

                let _ = self.fbuild.add_block(endif);

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
                let _ = self.fbuild.add_instr(Instr::Assign(
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
                let _ = self.fbuild.add_instr(Instr::Assign(
                    cond_res_tmp.clone(),
                Type::Long,
                    Box::new(cmp_instr)
                ));

                let _ = self.fbuild.add_instr(Instr::Jnz(
                        cond_res_tmp, 
                        body_lbl.clone(), // if true  
                        end.clone() // if false
                ));

                self.fbuild.add_block(body_lbl);

                let body_gd = self.gen_expr(body.node);
                if !body_gd.returned {
                    self.fbuild.add_instr(Instr::Jmp(loop_block));
                }

                let _ = self.fbuild.add_block(end);

                self.loop_exits.pop();
                self.loop_conts.pop();
            }
            AstNode::ForLoop { itervar, iter_upd, iter_cond, body } => {
                let itervar_gd = self.gen_expr(itervar.node);

                let loop_block = self.alloc_label();
                let body_block = self.alloc_label();
                let end_block = self.alloc_label();

                self.loop_conts.push(loop_block.clone());
                self.loop_exits.push(end_block.clone());

                let _ = self.fbuild.add_instr(Instr::Jmp(loop_block.clone()));
                let _ = self.fbuild.add_block(loop_block.clone());

                let iter_cond_gd = self.gen_expr(iter_cond.node);

                let _ = self.fbuild.add_instr(Instr::Jnz(
                    iter_cond_gd.val.unwrap(),
                    body_block.clone(),
                    end_block .clone(),
                ));

                let _ = self.fbuild.add_block(body_block);
                let body_gd = self.gen_expr(body.node);
                let iter_upd_gd = self.gen_expr(iter_upd.node);  
                if !body_gd.returned {
                    let _ = self.fbuild.add_instr(Instr::Jmp(loop_block));
                }

                let _ = self.fbuild.add_block(end_block);

                self.loop_exits.pop();
                self.loop_conts.pop();
            }
            AstNode::BreakLoop => {
                let exit = self.loop_exits.pop().unwrap();

                let _ = self.fbuild.add_instr(Instr::Jmp(exit));
                
                let blk_name = self.alloc_label();
                let _ = self.fbuild.add_block(blk_name); // making qbe stfu
            }
            AstNode::ContinueLoop => {
                let tgt = self.loop_conts.pop().unwrap();

                let _ = self.fbuild.add_instr(Instr::Jmp(tgt));
                
                let blk_name = self.alloc_label();
                let _ = self.fbuild.add_block(blk_name); // making qbe stfu
            }
            AstNode::ExternedFunc { name, args, ret_type } => {}
            AstNode::none => {}
            other => {
                panic!("can't generate yet for {:?}", other);
            }
        }
        if let Some(f) = self.fbuild.pop_func() {
            self.module.add_function(f);
        };
        if self.should_push {
            for (idx, v) in res.instrs.drain(..).enumerate() {
                self.fbuild.add_instr(v);
            }
        }
        return res;
    }

    fn gen_func(&mut self, name: String, args: Vec<FuncArg>, 
            ret_type: FType, body: Box<AstNode>, over_idx: usize)  {
        // TODO: pub 
        self.symb_table.push_funcargs(args.clone());

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
            format!("{}_{}", name, over_idx),
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

    fn get_conv(ft_src: FType, target_type: FType, src: Value) -> Instr {
        match (ft_src, target_type) {
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
            other => unimplemented!("Type conv: {:?} => {:?}",
                ft_src, target_type)
        }
    }

    fn gen_cmp_op(&mut self, cmp_op: CmpOp, op1: GenData, op2: GenData)
            -> Value {
        let tmp = self.new_temp();
        let val1 = op1.val.unwrap();
        let val2 = op2.val.unwrap();

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
                        Self::match_ft_qbf(op1.ftype),
                        qbe_cmp,
                        val1, val2
                    );

        self.fbuild.add_instr(Instr::Assign(
            tmp.clone(),
            Type::Word,
            Box::new(instr)
        ));

        tmp
    }

    fn leave_scope_clean(&mut self) {
        let dropped = self.symb_table.exit_scope();
        for val in dropped.iter() {
        }
    }

    /// presaves idx but wont push into sbuf
    fn alloc_label(&mut self) -> String {
        let name = format!("label_{}", self.labels.len());
        self.labels.insert(name.clone(), self.sbuf.len());
        name
    }

    pub fn match_ft_qbf(ft: FType) -> Type {
        match ft {
            FType::int | FType::uint  => Type::Long,
            FType::double             => Type::Double,
            FType::bool               => Type::Word, // qbe assignment rule
            FType::Array(el, _, _)    => {
                Self::match_ft_qbf(idx_to_ftype(el).unwrap())
            },
            FType::strconst         => Type::Long, // ptr
            other => todo!("Match ft qbf for {:?}", ft)
        }
    }

    pub fn sizeof(ft: FType) -> u64 {
        match ft {
            FType::int | FType::uint | FType::double => 8,
            FType::bool => 4, // word type for bool asignments 
            other => 8,
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
    
    fn gen_intrinsic(&mut self, intrin: Intrinsic, rightdat: GenData) 
            -> GenData {
        let mut resd = GenData::new();
        match intrin {
            Intrinsic::Print => {
                match Self::match_ft_qbf(rightdat.ftype) {
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

                                resd.instrs.push(
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

                                resd.instrs.push(
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

                                    resd.instrs.push(
                                        Instr::Call(
                                            "printf".into(),
                                            args, 
                                            None
                                        )
                                    );
                            }
                            other => unimplemented!()
                        }
                    }
                    Type::Double => {
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

    pub fn add_block<S>(&mut self, name: S) -> Result<(), ()>
        where S: Into<String> {
        if let Some(f) = self.func.as_mut() {
            f.add_block(name);
            Ok(())
        } else {
            Err(())
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
