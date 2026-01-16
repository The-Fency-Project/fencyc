use std::{collections::HashMap, fmt::format};

use crate::{
    fcparse::fcparse::{self as fparse, AstRoot, CmpOp},
    lexer::lexer::Intrinsic,
    seman::seman::{self as sem, idx_to_ftype, FSymbol, FType, SemAn, SymbolTable, VarPosition},
}; // AstNode;
use fparse::AstNode;

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
    pub dsbuf: String,
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
            dsbuf: String::new(),
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
        self.sbuf.push_str(
            "section text\n\
                            .start\n\
                            call @main_0\n\
                            halt\n",
        );
        while let Some(r) = self.ast.get(self.cur_ast) {
            let gdat = self.gen_expr(r.clone().node);
            self.cur_ast += 1;
        }

        self.sbuf.push_str("section data\n");
        self.sbuf.push_str(&self.dsbuf);
    }

    pub fn write_file(&mut self, fname: &str) -> Result<(), std::io::Error> {
        if let Some(parent) = std::path::Path::new(fname).parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(fname, &self.sbuf)?;

        Ok(())
    }

    fn gen_expr(&mut self, node: AstNode) -> GenData {
        let mut res = GenData::new(Vec::new());
        match node {
            AstNode::Assignment { name, val, ft } => {
                let rightdat = self.gen_expr(*val);

                // Array(usize, usize, usize) // typeid, count, arridx
                if let FType::Array(typeid, _, _) = ft {
                    // TODO: either add support for getting the same array,
                    // or deny that idea completely.
                    let mut count: Option<usize> = None;
                    rightdat.arrd.inspect(|x| {count = Some(x.len)});

                    let arr_idx = self.arrays.len();
                    let is_new: bool = count.is_some();
                    
                    let rdst = self.alloc_reg(ValDat::Symbol(FSymbTabData::new(
                        self.symb_table.cur_scope,
                        name.clone(),
                    )));

                    if is_new {
                        self.sbuf
                           .push_str(&format!("dslea r{} array{} 9\n", rdst, arr_idx));
                        self.arrays.insert(name.clone(), ArrayData::new(
                            self.arrays.len(),
                            count.unwrap(), // has to be some here
                            idx_to_ftype(typeid).expect("internal: unknown ftype")
                        )); 
                    } else {
                        self.sbuf
                           .push_str(&format!("movr r{} r{}\n", rdst, rightdat.alloced_regs[0]));
                    }

                    res.alloced_regs.push(rdst);
                    
                    let mut symb = FSymbol::new(name.clone(), 
                        sem::VarPosition::Register(rightdat.alloced_regs[0]), 
                        ft
                    );
                    
                    if is_new {
                        symb.dsname = Some(format!("array{}", arr_idx));
                    } else {
                        panic!("Internal error: array isn't new");  
                    };
                    
                    symb.cur_reg = VarPosition::Register(rdst);
                    self.symb_table.newsymb(symb);
                    
                    self.free_reg_not_var(rightdat.alloced_regs[0]);
                    return res;
                }
                let mut symb = FSymbol::new(name.clone(), sem::VarPosition::Register(0), ft);
                let leftreg = self.alloc_reg(ValDat::Symbol(FSymbTabData::new(
                    self.symb_table.cur_scope,
                    name.clone(),
                )));
                symb.cur_reg = VarPosition::Register(leftreg);

                res.alloced_regs.push(leftreg);

                let mut instr = String::new();
                instr = format!("movr r{} r{}\n", leftreg, rightdat.alloced_regs[0]);

                self.symb_table.newsymb(symb);
                res.expr_type = ft;
                self.sbuf.push_str(&instr);
                self.free_reg_not_var(rightdat.alloced_regs[0]);
            }
            AstNode::Int(iv) => {
                let reg = self.alloc_reg(ValDat::ImmVal(Numerical::int(iv)));
                let instr = format!("iload r{} {}\n", reg, iv);
                res.alloced_regs.push(reg);
                res.expr_type = FType::int;
                self.sbuf.push_str(&instr);
            }
            AstNode::Float(fv) => {
                let reg = self.alloc_reg(ValDat::ImmVal(Numerical::float(fv)));
                let instr = format!("fload r{} {:#?}\n", reg, fv);
                // :#? so it would always be with point. its important for voxasm
                res.alloced_regs.push(reg);
                res.expr_type = FType::float;
                self.sbuf.push_str(&instr);
            }
            AstNode::Uint(uv) => {
                let reg = self.alloc_reg(ValDat::ImmVal(Numerical::uint(uv)));
                let instr = format!("uload r{} {}\n", reg, uv);
                res.alloced_regs.push(reg);
                res.expr_type = FType::uint;
                self.sbuf.push_str(&instr);
            }
            AstNode::boolVal(bv) => {
                let reg = self.alloc_reg(ValDat::ImmVal(Numerical::boolean(bv)));
                let instr = format!("uload r{} {}\n", reg, bv as u64);
                res.alloced_regs.push(reg);
                res.expr_type = FType::bool;
                self.sbuf.push_str(&instr);
            }
            AstNode::BinaryOp { op, left, right } => {
                let leftdat = self.gen_expr(*left);
                let rightdat = self.gen_expr(*right);
                res.expr_type = leftdat.expr_type; // assuming semantic analyzer already checked it

                let mut instr = String::new();
                let ftlet = CodeGen::ftletter(leftdat.expr_type);
                let need_save = leftdat.alloced_regs[0] == rightdat.alloced_regs[0];
                if need_save {
                    self.sbuf
                        .push_str(&format!("push r{}\n", leftdat.alloced_regs[0]));
                }
                match op {
                    fparse::BinaryOp::Add => {
                        instr = format!(
                            "{}add r{} r{}\n",
                            ftlet, leftdat.alloced_regs[0], rightdat.alloced_regs[0],
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::Substract => {
                        instr = format!(
                            "{}sub r{} r{}\n",
                            ftlet, leftdat.alloced_regs[0], rightdat.alloced_regs[0],
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::Multiply => {
                        instr = format!(
                            "{}mul r{} r{}\n",
                            ftlet, leftdat.alloced_regs[0], rightdat.alloced_regs[0],
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::Divide => {
                        instr = format!(
                            "{}div r{} r{} r{}\n",
                            ftlet,
                            leftdat.alloced_regs[0],
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::Remainder => {
                        instr = format!(
                            "{}rem r{} r{} r{}\n",
                            ftlet,
                            leftdat.alloced_regs[0],
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0]
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::BitwiseAnd => {
                        instr = format!(
                            "and r{} r{}\n",
                            leftdat.alloced_regs[0], rightdat.alloced_regs[0]
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::BitwiseOr => {
                        instr = format!(
                            "or r{} r{}\n",
                            leftdat.alloced_regs[0], rightdat.alloced_regs[0]
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::BitwiseXor => {
                        instr = format!(
                            "xor r{} r{}\n",
                            leftdat.alloced_regs[0], rightdat.alloced_regs[0]
                        );
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::BitShiftLeft => {
                        let res_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                        res.alloced_regs.push(res_reg);
                        let leftreg = leftdat.alloced_regs[0];
                        let rightreg = rightdat.alloced_regs[0];

                        instr = format!(
                            "movr r{} r{}\n\
                                        shl r{} r{}\n",
                            res_reg, leftreg, res_reg, rightreg
                        );
                    }
                    fparse::BinaryOp::BitShiftRight => {
                        let res_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                        res.alloced_regs.push(res_reg);
                        let leftreg = leftdat.alloced_regs[0];
                        let rightreg = rightdat.alloced_regs[0];

                        instr = format!(
                            "movr r{} r{}\n\
                                        shr r{} r{}\n",
                            res_reg, leftreg, res_reg, rightreg
                        );
                    }
                    fparse::BinaryOp::Compare(cmp_op) => {
                        let leftreg = leftdat.alloced_regs[0];
                        let rightreg = rightdat.alloced_regs[0];
                        self.sbuf
                            .push_str(&format!("{}cmp r{} r{}\n", ftlet, leftreg, rightreg));

                        let label_true = self.alloc_label();
                        let jmpinstr = CodeGen::match_jmp_op(cmp_op, &label_true);
                        self.sbuf.push_str(&jmpinstr);

                        let exit_lbl = self.alloc_label();
                        self.sbuf.push_str(&format!(
                            "uload r{} 0\n\
                                        jmp @{}\n",
                            leftreg, exit_lbl
                        ));

                        self.push_label(&label_true);
                        self.sbuf.push_str(&format!("uload r{} 1\n", leftreg));
                        self.push_label(&exit_lbl);

                        self.free_reg_not_var(rightreg);
                        res.alloced_regs.push(leftreg);
                    }
                    other => {
                        panic!("Unknown binary operation type: {:?}", other);
                    }
                }
                if need_save {
                    self.sbuf
                        .push_str(&format!("pop r{}\n", leftdat.alloced_regs[0]));
                }

                self.sbuf.push_str(&instr);
                self.free_reg_not_var(rightdat.alloced_regs[0]);
            }
            AstNode::Variable(av) => {
                self.load_variable(av, &mut res);

            }
            AstNode::CodeBlock { exprs } => {
                self.symb_table.enter_scope();
                for expr in exprs {
                    self.gen_expr(expr.node);
                }
                self.leave_scope_clean();
            }
            AstNode::Reassignment { name, newval } => {
                let var_name = name.clone();

                let rhdat = self.gen_expr(newval.node);

                let varreg = {
                    let entry = self.symb_table.get(var_name.clone()).unwrap();
                    let scope = entry.0;
                    match entry.1.cur_reg {
                        VarPosition::Register(ri) => ri,
                        VarPosition::None => panic!("None var value!"),
                        VarPosition::Stack(sfi) => {
                            self.extract_reg(sfi, ValDat::Symbol(FSymbTabData::new(scope, name)))
                        }
                    }
                };

                let instr = format!("movr r{} r{}\n", varreg, rhdat.alloced_regs[0]);
                self.sbuf.push_str(&instr);

                if let Some(entry) = self.symb_table.get_mut(var_name) {
                    entry.1.cur_reg = VarPosition::Register(varreg);
                }

                self.free_reg_not_var(rhdat.alloced_regs[0]);
            }
            AstNode::IfStatement {
                cond,
                if_true,
                if_false,
            } => {
                let cond_dat = self.gen_expr(cond.node);
                let reg = cond_dat.alloced_regs[0];
                let test_instr = format!("test r{} r{}\n", reg, reg);
                self.sbuf.push_str(&test_instr);

                let jumpf_instr = format!("jz @label_{}\n", self.labels.len());
                self.sbuf.push_str(&jumpf_instr);

                let false_labelname = self.alloc_label();
                let exit_labelname = self.alloc_label();

                self.gen_expr(if_true.node);

                let jumpe_instr = format!("jmp @{}\n", &exit_labelname);
                self.sbuf.push_str(&jumpe_instr);

                self.push_label(&false_labelname);
                self.symb_table.enter_scope();
                if let Some(ve) = if_false {
                    self.gen_expr(ve.node);
                }
                self.leave_scope_clean();
                self.push_label(&exit_labelname);
            }
            AstNode::VariableCast { name, target_type } => {
                let dst_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                res.alloced_regs.push(dst_reg);

                let vartype: FType = match self.symb_table.get(name.clone()) {
                    Some(v) => v.1.ftype,
                    None => {
                        panic!("undeclared {}", name);
                    }
                };
                if vartype == target_type {
                    return res;
                }

                let reg_var = self.load_variable(name, &mut res);

                let ftlet_src = CodeGen::ftletter(vartype);
                let ftlet_dst = CodeGen::ftletter(target_type);
                if ftlet_src == ftlet_dst {
                    // additional check bc ftletters can collide
                    if target_type == FType::bool {
                        let instr = format!("test r{} r{}\n", dst_reg, reg_var);

                        self.sbuf.push_str(&instr);
                    }
                    return res;
                }

                let instr = format!("{}to{} r{} r{}\n", ftlet_src, ftlet_dst, dst_reg, reg_var);
                self.sbuf.push_str(&instr);

                if target_type == FType::bool {
                    let lnot_instr = format!("lnot r{} r{}\n", dst_reg, dst_reg);
                    let notd_instr = format!("lnot r{} r{}\n", dst_reg, dst_reg);

                    // again but for other cases
                    self.sbuf.push_str(&lnot_instr);
                    self.sbuf.push_str(&notd_instr);
                }
            }
            AstNode::ExprCast { expr, target_type } => {
                let exprgen = self.gen_expr(*expr);
                let src_reg = exprgen.alloced_regs[0];
                self.free_reg_not_var(src_reg);

                let dst_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                res.alloced_regs.push(dst_reg);

                let exprtype = exprgen.expr_type;
                if exprtype == target_type {
                    return res;
                }

                let ftlet_src = CodeGen::ftletter(exprtype);
                let ftlet_dst = CodeGen::ftletter(target_type);
                if ftlet_src == ftlet_dst {
                    // additional check bc ftletters can collide
                    if target_type == FType::bool {
                        let lnot_instr = format!("lnot r{} r{}\n", dst_reg, src_reg);
                        let notd_instr = format!("lnot r{} r{}\n", dst_reg, dst_reg);

                        // in other words: !!var = var (but logically)
                        self.sbuf.push_str(&lnot_instr);
                        self.sbuf.push_str(&notd_instr);
                    }
                    return res;
                }

                let instr = format!("{}to{} r{} r{}\n", ftlet_src, ftlet_dst, dst_reg, src_reg);
                self.sbuf.push_str(&instr);

                if target_type == FType::bool {
                    let lnot_instr = format!("lnot r{} r{}\n", dst_reg, dst_reg);
                    let notd_instr = format!("lnot r{} r{}\n", dst_reg, dst_reg);

                    // again but for other cases
                    self.sbuf.push_str(&lnot_instr);
                    self.sbuf.push_str(&notd_instr);
                }
            }
            AstNode::Intrinsic { intr, val } => {
                if matches!(intr, Intrinsic::Len) {
                    match *val {
                        AstNode::Variable(name) => {
                            let arr_len = match self.arrays.get(&name) {
                                Some(v) => v.len,
                                None => panic!("Internal error: can't get\
                                    array for len intrin")
                            };

                            let reg = self.alloc_reg(ValDat::ImmVal(
                                    Numerical::uint(arr_len as u64)
                            ));
                            self.sbuf.push_str(&format!("uload r{} {}\n",
                                reg, arr_len
                            ));
                            res.alloced_regs.push(reg);

                        }
                        other => {todo!("Could only get _len for variables")}
                    }
                    return res;
                }

                let rdat = self.gen_expr(*val);
                self.gen_intrinsic(intr, rdat.alloced_regs[0]);
            }
            AstNode::UnaryOp { op, expr } => {
                let rdat = self.gen_expr(*expr);
                res.expr_type = rdat.expr_type;

                let dst_reg = rdat.alloced_regs[0];

                let instr = match op {
                    fparse::UnaryOp::Negate => {
                        let ftletter = CodeGen::ftletter(rdat.expr_type);
                        format!("{}neg r{} r{}\n", ftletter, dst_reg, dst_reg)
                    }
                    fparse::UnaryOp::Not => {
                        format!("not r{} r{}\n", dst_reg, dst_reg)
                    }
                    fparse::UnaryOp::LogicalNot => {
                        format!("lnot r{} r{}\n", dst_reg, dst_reg)
                    }
                };
                self.sbuf.push_str(&instr);
                res.alloced_regs.push(rdat.alloced_regs[0]);
            }
            AstNode::WhileLoop { cond, body } => {
                self.symb_table.enter_scope();

                let loop_lab = self.new_label();
                self.loop_conts.push(loop_lab.clone());
                let exit_lab = self.alloc_label();
                self.loop_exits.push(exit_lab.clone());

                let cond_gen = self.gen_expr(cond.node);
                let cond_reg = cond_gen.alloced_regs[0];

                self.sbuf
                    .push_str(&format!("test r{} r{}\n", cond_reg, cond_reg));
                self.sbuf.push_str(&format!("jz @{}\n", &exit_lab));

                self.gen_expr(body.node);

                self.sbuf.push_str(&format!("jmp @{}\n", loop_lab));
                self.push_label(&exit_lab);

                if let Some(_) = self.loop_exits.last() {
                    self.loop_exits.pop();
                };
                if let Some(_) = self.loop_conts.last() {
                    self.loop_conts.pop();
                };

                self.symb_table.exit_scope();
            }
            AstNode::ForLoop {
                itervar,
                iter_upd,
                iter_cond,
                body,
            } => {
                self.symb_table.enter_scope();
                let itergen = self.gen_expr(itervar.node);

                let loop_lab = self.new_label();
                let exit_lab = self.alloc_label();
                self.loop_exits.push(exit_lab.clone());

                let upd_lbl = self.alloc_label();
                self.loop_conts.push(upd_lbl.clone());

                let itercond_gen = self.gen_expr(iter_cond.node);
                self.sbuf.push_str(&format!("jz @{}\n", exit_lab));

                let body_gen = self.gen_expr(body.node);

                self.push_label(&upd_lbl);
                let iterupd_gen = self.gen_expr(iter_upd.node);
                self.sbuf.push_str(&format!("jmp @{}\n", loop_lab));
                self.push_label(&exit_lab);

                if let Some(_) = self.loop_exits.last() {
                    self.loop_exits.pop();
                };
                if let Some(_) = self.loop_conts.last() {
                    self.loop_conts.pop();
                };

                self.symb_table.exit_scope();
            }
            AstNode::BreakLoop => {
                let loop_label = match self.loop_exits.last() {
                    // break from nearest loop
                    Some(v) => v,
                    None => panic!("Internal error: can't get loop exit label"),
                };

                self.sbuf.push_str(&format!("jmp @{}\n", loop_label));
            }
            AstNode::ContinueLoop => {
                let loop_label = match self.loop_conts.last() {
                    Some(v) => v,
                    None => panic!("Internal error: can't get loop continue label"),
                };

                self.sbuf.push_str(&format!("jmp @{}\n", loop_label));
            }
            AstNode::Function {
                name,
                args,
                ret_type,
                body,
            } => {
                self.stackidxs.push(self.predicted_stack.len());

                self.sbuf
                    .push_str(&format!("func {}_{}\n", &name, self.overload_ctr));
                self.symb_table.enter_scope();
                self.symb_table.push_funcargs(args.clone());
                for (idx, val) in args.iter().enumerate() {
                    self.alloced_regs[idx + 1] = ValDat::Symbol(FSymbTabData::new(
                        self.symb_table.cur_scope,
                        val.name.clone(),
                    ));
                }

                self.gen_expr(*body);

                let cur_len = self.predicted_stack.len();
                let tgt_len = self
                    .stackidxs
                    .pop()
                    .unwrap_or_else(|| panic!("Internal error: can't get stackidx"));
                // poping stack until we get to prev val
                for i in (tgt_len..cur_len).rev() {
                    self.sbuf.push_str("pop r31");
                }

                self.symb_table.exit_scope();

                for val in self.alloced_regs.iter_mut().skip(1) {
                    *val = ValDat::None;
                }
            }
            AstNode::FunctionOverload { func, idx } => {
                self.overload_ctr = idx;
                self.gen_expr(*func);
                self.overload_ctr = 0;
            }
            AstNode::ReturnVal { val } => {
                if !matches!(val.node, AstNode::none) {
                    let valdat = self.gen_expr(val.node);

                    self.sbuf
                        .push_str(&format!("movr r0 r{}\n", valdat.alloced_regs[0]));
                }
                self.sbuf.push_str(&format!("ret\n"));
            }
            AstNode::Call {
                func_name,
                args,
                idx,
            } => {
                // better perf
                let mut args_sf = Vec::new(); // args stack frames idxs
                for (idx, val) in args.iter().enumerate() {
                    let gdat = self.gen_expr(val.node.clone());
                    self.sbuf
                        .push_str(&format!("push r{}\n", gdat.alloced_regs[0]));
                    args_sf.push(self.predicted_stack.len());
                    self.predicted_stack.push(ValDat::ImmVal(Numerical::None));
                }

                for (idx, sfi) in args_sf.iter().rev().enumerate() {
                    if *sfi == self.predicted_stack.len().saturating_sub(1) {
                        self.sbuf.push_str(&format!("pop r{}\n", idx + 1));
                        self.predicted_stack.pop();
                    } else {
                        self.sbuf.push_str(&format!(
                            "
                                            uload r0 {}\n\
                                            gsf r{} r0\n\
                                            usf r0 r0\n",
                            sfi,
                            idx + 1
                        ));
                        self.predicted_stack[*sfi] = ValDat::None;
                    }
                }

                self.sbuf.push_str(&"pushall\n"); // TODO: push only used registers for
                let overload_idx = self.matched_overloads.get(&idx).unwrap_or_else(|| {
                    panic!("{}: internal error: can't get matched overload", &func_name);
                });
                self.sbuf.push_str(&format!(
                    "call @{}_{}\n\
                                            popall\n",
                    &func_name, *overload_idx
                ));
                res.alloced_regs.push(0);
            }
            AstNode::Array(ft, nodes) => {
                if nodes.len() == 0 {
                    panic!("codegen error: array couldnt have 0 size");
                }

                let mut decl = format!("array{} {:?}[{}] [", self.arrays.len(), ft, nodes.len());

                for (idx, node) in nodes.iter().enumerate() {
                    if idx > 0 {
                        decl.push_str(", ");
                    }
                    match node {
                        AstNode::Uint(uv) => {
                            decl.push_str(&format!("{}", uv));
                        }
                        AstNode::Int(iv) => {
                            decl.push_str(&format!("{}", iv));
                        }
                    AstNode::Float(fv) => {
                            decl.push_str(&format!("{:#?}", fv));
                        }
                        other => {
                            panic!("Codegen error: invalid array member {:#?}", other);
                        }
                    }
                }

                decl.push_str("]\n");
                self.dsbuf.push_str(&decl);

                let dst_reg = self.alloc_reg(ValDat::ImmVal(Numerical::uint(0)));
                self.sbuf.push_str(&format!(
                        "dslea r{} array{} 9\n"
                , dst_reg, self.arrays.len()));

                res.alloced_regs.push(dst_reg); 
                res.arrd = Some(ArrayData::new(
                        self.arrays.len(), nodes.len(), ft
                ));

                // we'd expect assignment to push new entry into 
                // arrays hashmap
            }
            // the code below is even dirtier and defly need some refactor
            AstNode::ArrayElem(arr_name, idx_ast) => {
                let mut idx_val: Option<usize> = None;
                let mut dst_reg: usize = 33;
                let idx_gendat: Option<GenData> = match &idx_ast.node {
                    AstNode::Uint(uv) => {
                        dst_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                        idx_val = Some(*uv as usize);
                        None
                    }
                    other => {
                        let gd = self.gen_expr(other.clone());
                        dst_reg = gd.alloced_regs[0];
                        Some(gd)
                    }
                };

                let mut arrn_ds = String::new(); // ds name
                let mut elem_size: usize = 0;

                if let Some(entry) = self.symb_table.get(arr_name.clone()) {
                    arrn_ds = match &entry.1.dsname {
                        Some(v) => v.clone(),
                        None => panic!("Internal error: can't get ds name for symbol {}", arr_name),
                    };
                    let el_type_idx = match entry.1.ftype {
                        FType::Array(fti, _, _) => fti, // TODO
                        other => panic!("Unexpected type {:?} for {}", other, arr_name),
                    };
                    let el_type = idx_to_ftype(el_type_idx).unwrap_or_else(|| {
                        panic!("Internal error: no type for {}", el_type_idx);
                    });
                    elem_size = CodeGen::match_ftype_size(el_type);
                } else {
                    unreachable!(
                        "Internal error: no array {} in codegen symbol table",
                        arr_name
                    );
                }

                let instr = match (idx_val, idx_gendat) {
                    (Some(idx), None) => {
                        format!("dsload r{} {} {}\n", dst_reg, arrn_ds, idx * elem_size)
                    }
                    (None, Some(gd)) => {
                        let size_reg =
                            self.alloc_reg(ValDat::ImmVal(Numerical::uint(elem_size as u64)));
                        format!(
                            "uload r{} {}\n\
                            umul r{} r{}\n\
                            dsrload r{} r{} {}\n",
                            size_reg, elem_size, dst_reg, size_reg, dst_reg, dst_reg, arrn_ds
                        )
                    }
                    other => unreachable!("Internal error: got {:?} in arr_el", other),
                };

                self.sbuf.push_str(&instr);
                res.alloced_regs.push(dst_reg);
            }
            other => {
                panic!("can't generate yet for {:?}", other);
            }
        }
        return res;
    }

    /// loads variable in place and returns register idx
    fn load_variable(&mut self, name: String, gend: &mut GenData) -> usize {
        let (scope, vsymb) = self
            .symb_table
            .get(name.clone())
            .expect(&format!("No variable {} in scope", name));
        let var_name = vsymb.name.clone();
        gend.expr_type = vsymb.ftype;
        match vsymb.cur_reg {
            sem::VarPosition::None => {
                panic!("None value for {}!", vsymb.name);
            }
            sem::VarPosition::Register(ri) => {
                self.sbuf.push_str(&format!("push r{}\n", ri)); // for safety
                let dst_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                gend.alloced_regs.push(dst_reg);
                self.sbuf.push_str(&format!("pop r{}\n", dst_reg));
                dst_reg
            }
            sem::VarPosition::Stack(sfi) => {
                let mut instr = String::new();
                let reg = self.alloc_reg(ValDat::Symbol(FSymbTabData::new(scope, var_name)));
                if self.stack_end == sfi {
                    instr = format!("pop r{}\n", reg);
                    self.predicted_stack.pop();
                } else {
                    let reg_zero = self.alloc_reg(ValDat::ImmVal(Numerical::uint(0)));
                    instr = format!(
                        "gsf r{} r{}\n
                         uload r{} 0\n
                         usf r{} r{}\n",
                        reg, sfi, reg_zero, reg, reg_zero,
                    );
                }
                self.sbuf.push_str(&instr);
                reg
            }
        }
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
            match val {
                sem::VarPosition::None => {}
                sem::VarPosition::Register(ri) => {
                    self.free_reg(*ri);
                    let instr = format!("uload r{} 0\n", ri);
                    self.sbuf.push_str(&instr);
                }
                sem::VarPosition::Stack(sfi) => {
                    let reg_idx = self.alloc_reg(ValDat::ImmVal(Numerical::uint(*sfi as u64)));
                    let reg_zero = self.alloc_reg(ValDat::ImmVal(Numerical::uint(0)));
                    let instr = format!(
                        "uload r{} {}\n
                         uload r{} {}\n 
                         usf r{} r{}",
                        reg_idx, sfi, reg_zero, 0, reg_idx, reg_zero
                    );
                    self.sbuf.push_str(&instr);
                    self.free_reg(reg_idx);
                    self.free_reg(reg_zero);
                }
            }
        }
    }

    fn alloc_reg(&mut self, val: ValDat) -> usize {
        // 1. Find any truly free register
        for i in 0..self.alloced_regs.len() {
            if matches!(self.alloced_regs[i], ValDat::None) {
                self.alloced_regs[i] = val;
                return i;
            }
        }

        for i in (0..self.alloced_regs.len()).rev() {
            if !matches!(self.alloced_regs[i], ValDat::Symbol(_)) {
                self.spill_and_use(i, val);
                return i;
            }
        }

        let spill_reg = self.alloced_regs.len() - 1; // R31
        self.spill_and_use(spill_reg, val);
        spill_reg
    }

    fn spill_and_use(&mut self, reg: usize, new_val: ValDat) {
        if !matches!(self.alloced_regs[reg], ValDat::None) {
            self.sbuf.push_str(&format!("push r{}\n", reg));
            if let ValDat::Symbol(s) = &self.alloced_regs[reg].clone() {
                if let Some(entry) = self.symb_table.get_mut_in_scope(&s.name, s.scope) {
                    entry.cur_reg = VarPosition::Stack(self.stack_end);
                }
            }
            self.stack_end += 1;
        }

        self.alloced_regs[reg] = new_val;
    }

    fn free_reg_not_var(&mut self, idx: usize) {
        if let Some(ValDat::Symbol(_)) = &self.alloced_regs.get(idx) {
            return;
        }
        self.alloced_regs[idx] = ValDat::None;
    }

    fn free_reg(&mut self, idx: usize) {
        if let Some(ValDat::Symbol(s)) = &self.alloced_regs.get(idx) {
            if let Some(val) = self.symb_table.get_mut_in_scope(&s.name, s.scope) {
                if let VarPosition::Register(_) = val.cur_reg {
                    val.cur_reg = VarPosition::None;
                }
            };
        }
        self.alloced_regs[idx] = ValDat::None;
    }

    fn extract_reg(&mut self, sfi: usize, val: ValDat) -> usize {
        let dstreg = self.alloc_reg(val);
        if sfi == self.predicted_stack.len().saturating_sub(1) {
            let instr = format!("pop r{}\n", dstreg);
            self.sbuf.push_str(&instr);
        } else {
            let idx_reg = self.alloc_reg(ValDat::ImmVal(Numerical::uint(sfi as u64)));
            let instr = format!(
                "uload r{} {}\n
                gsf r{} r{}\n",
                idx_reg, sfi, dstreg, idx_reg
            );
            self.sbuf.push_str(&instr);
            self.free_reg(idx_reg);
        }
        dstreg
    }

    fn get_typeconv(ftyp_src: FType, ftyp_dst: FType, rd: usize, rs: usize) -> String {
        let ft1_l = CodeGen::ftletter(ftyp_src);
        let ft2_l = CodeGen::ftletter(ftyp_dst);
        format!("{}to{} r{} r{}\n", ft1_l, ft2_l, rd, rs)
    }

    fn ftletter(ftype: FType) -> &'static str {
        match ftype {
            FType::int => "i",
            FType::float => "f",
            FType::heapptr => "p",
            _ => "u",
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
#[derive(Debug)]
pub struct GenData {
    pub alloced_regs: Vec<usize>,
    pub symbols: HashMap<String, FSymbol>,
    pub expr_type: FType,
    pub cmp_op: Option<CmpOp>,
    pub arrd: Option<ArrayData>,
}

impl GenData {
    pub fn new(alloced: Vec<usize>) -> GenData {
        GenData {
            alloced_regs: alloced,
            symbols: HashMap::new(),
            expr_type: FType::none,
            cmp_op: None,
            arrd: None,
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
