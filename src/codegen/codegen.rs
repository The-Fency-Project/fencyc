use std::{collections::HashMap};

use crate::{fcparse::fcparse::{self as fparse, AstRoot}, lexer::lexer::Intrinsic, seman::seman::{self as sem, FSymbol, FType, SymbolTable, VarPosition}};// AstNode;
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
    None
}

#[derive(Debug)]
pub struct CodeGen {
    ast: Vec<AstRoot>,
    cur_ast: usize,
    pub sbuf: String,
    alloced_regs: Vec<ValDat>,
    unused_regs: Vec<usize>, // which are unused for some time (lru)
    pub symb_table: SymbolTable,
    predicted_stack: Vec<ValDat>,
    stack_end: usize, // latest stack frame idx
    labels: HashMap<String, usize> // usize for sbuf idx 
}

impl CodeGen {
    pub fn new(ast: Vec<AstRoot>) -> CodeGen {
        CodeGen { 
            ast: ast, 
            cur_ast: 0,
            sbuf: String::new(),
            alloced_regs: vec![ValDat::None; 32],
            unused_regs: Vec::new(),
            symb_table: SymbolTable::new(),
            stack_end: 0,
            predicted_stack: Vec::new(),
            labels: HashMap::new()
        }
    }

    pub fn gen_everything(&mut self) {
        while let Some(r) = self.ast.get(self.cur_ast) {
            let gdat = self.gen_expr(r.clone().node);
            self.cur_ast += 1;
        }
        self.sbuf.push_str("halt\n"); // TODO: move it to main() end 
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
                
                let mut symb = FSymbol::new(
                    name.clone(), sem::VarPosition::Register(0), ft
                );
                let leftreg = self.alloc_reg(
                    ValDat::Symbol(FSymbTabData::new(
                        self.symb_table.cur_scope, 
                        name.clone()    
                    ))
                );
                symb.cur_reg = VarPosition::Register(leftreg);

                res.alloced_regs.push(leftreg);

                let mut instr = String::new();
                instr = format!("movr r{} r{}\n",
                        leftreg, rightdat.alloced_regs[0]);
               
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
            },
            AstNode::Float(fv) => {
                let reg = self.alloc_reg(ValDat::ImmVal(Numerical::float(fv)));
                let instr = format!("fload r{} {:#?}\n", reg, fv); 
                // :#? so it would always be with point. its important for voxasm
                res.alloced_regs.push(reg);
                res.expr_type = FType::float;
                self.sbuf.push_str(&instr);
            },
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

                let mut instr = String::new();
                let ftlet = CodeGen::ftletter(leftdat.expr_type);
                let need_save = leftdat.alloced_regs[0] == rightdat.alloced_regs[0];
                if need_save {
                    self.sbuf.push_str(&format!("push r{}\n", leftdat.alloced_regs[0]));
                }
                match op {
                    fparse::BinaryOp::Add => {
                        instr = format!("{}add r{} r{}\n", 
                            ftlet,
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        ); 
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    } 
                    fparse::BinaryOp::Substract => {
                        instr = format!("{}sub r{} r{}\n", 
                            ftlet,
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        ); 
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::Multiply => {
                        instr = format!("{}mul r{} r{}\n",
                            ftlet,
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        ); 
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    } 
                    fparse::BinaryOp::Divide => {
                        instr = format!("{}div r{} r{} r{}\n", 
                            ftlet,
                            leftdat.alloced_regs[0],
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        ); 
                        res.alloced_regs.push(leftdat.alloced_regs[0]); 
                    }
                    fparse::BinaryOp::BitwiseAnd => {
                        instr = format!("and r{} r{}\n",
                            leftdat.alloced_regs[0], rightdat.alloced_regs[0]);
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::BitwiseOr => {
                        instr = format!("or r{} r{}\n",
                            leftdat.alloced_regs[0], rightdat.alloced_regs[0]);
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::BitwiseXor => {
                        instr = format!("xor r{} r{}\n",
                            leftdat.alloced_regs[0], rightdat.alloced_regs[0]);
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::BitShiftLeft => {
                        let res_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                        res.alloced_regs.push(res_reg);
                        let leftreg = leftdat.alloced_regs[0];
                        let rightreg = rightdat.alloced_regs[0];

                        instr = format!("movr r{} r{}\n\
                                        shl r{} r{}\n",
                        res_reg, leftreg, res_reg, rightreg);
                    }
                    fparse::BinaryOp::BitShiftRight => {
                        let res_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                        res.alloced_regs.push(res_reg);
                        let leftreg = leftdat.alloced_regs[0];
                        let rightreg = rightdat.alloced_regs[0];

                        instr = format!("movr r{} r{}\n\
                                        shr r{} r{}\n",
                        res_reg, leftreg, res_reg, rightreg);
                    }
                    other => {
                        panic!("Unknown binary operation type: {:?}", other);
                    }
                }
                if need_save {
                    self.sbuf.push_str(&format!("pop r{}\n", leftdat.alloced_regs[0]));
                }

                self.sbuf.push_str(&instr);
                self.free_reg_not_var(rightdat.alloced_regs[0]);
            },
            AstNode::Variable(av) => {
                self.load_variable(av, &mut res);
            }
            AstNode::EnterScope => {
                self.symb_table.enter_scope();
            }, 
            AstNode::LeftScope => {
                self.leave_scope_clean(); 
            },
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
                            self.extract_reg(sfi, 
                                ValDat::Symbol(
                                    FSymbTabData::new(scope, name)
                                )
                            )
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
            AstNode::IfStatement { cond, if_true, if_false } => {
                let cond_dat = self.gen_expr(cond.node);
                let reg = cond_dat.alloced_regs[0];
                let test_instr = format!("test r{} r{}\n", reg, reg);
                self.sbuf.push_str(&test_instr);

                let jumpf_instr = format!("jz @label_{}\n", self.labels.len());
                self.sbuf.push_str(&jumpf_instr);

                let false_labelname = self.alloc_label();
                let exit_labelname = self.alloc_label();
                
                let mut iftrue_exprs: Vec<GenData> = Vec::new();
                self.symb_table.enter_scope();
                for expr in if_true {
                    iftrue_exprs.push(self.gen_expr(expr.node));
                }
                self.leave_scope_clean();
                let jumpe_instr = format!("jmp @{}\n", &exit_labelname);
                self.sbuf.push_str(&jumpe_instr);

                self.push_label(&false_labelname);
                self.symb_table.enter_scope();
                if let Some(ve) = if_false {
                    for expr in ve {
                        self.gen_expr(expr.node);
                    }
                }
                self.leave_scope_clean();
                self.push_label(&exit_labelname); 
            }
            AstNode::VariableCast { name, target_type } => {
                let dst_reg = self.alloc_reg(ValDat::ImmVal(Numerical::None));
                res.alloced_regs.push(dst_reg);

                let vartype: FType = match self.symb_table.get(name.clone()) {
                    Some(v) => v.1.ftype,
                    None => {panic!("undeclared {}", name);}
                };
                if vartype == target_type {
                    return res;
                }

                let reg_var = self.load_variable(name, &mut res);

                let ftlet_src = CodeGen::ftletter(vartype);
                let ftlet_dst = CodeGen::ftletter(target_type);
                if ftlet_src == ftlet_dst { // additional check bc ftletters can collide
                    if target_type == FType::bool {
                        let lnot_instr = format!("lnot r{} r{}\n", dst_reg, reg_var);
                        let notd_instr = format!("lnot r{} r{}\n", dst_reg, dst_reg);

                        // in other words: !!var = var (but logically)
                        self.sbuf.push_str(&lnot_instr);
                        self.sbuf.push_str(&notd_instr);
                    }
                    return res;
                }

                let instr = format!("{}to{} r{} r{}\n",
                    ftlet_src, ftlet_dst, dst_reg, reg_var);
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
                let rdat = self.gen_expr(*val);
                self.gen_intrinsic(intr, rdat.alloced_regs[0]);
            }
            AstNode::UnaryOp { op, expr } => {
                let rdat = self.gen_expr(*expr);

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
            other => {
                panic!("can't generate yet for {:?}", other);
            }
        }
        return res;
    }

    /// loads variable in place and returns register idx
    fn load_variable(&mut self, name: String, gend: &mut GenData)
        -> usize {
        let (scope, vsymb) = self.symb_table.get(name.clone())
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
                let reg = self.alloc_reg(
                    ValDat::Symbol(FSymbTabData::new(
                        scope, var_name
                    ))
                );
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

    fn leave_scope_clean(&mut self) {
        let dropped = self.symb_table.exit_scope();
        for val in dropped.iter() {
            match val {
                sem::VarPosition::None => {}
                sem::VarPosition::Register(ri) => {
                    self.free_reg(*ri);
                    let instr = format!("uload r{} 0\n",
                        ri);
                    self.sbuf.push_str(&instr);
                }
                sem::VarPosition::Stack(sfi) => {
                    let reg_idx = self.alloc_reg(
                        ValDat::ImmVal(Numerical::uint(*sfi as u64))
                    );
                    let reg_zero = self.alloc_reg(
                        ValDat::ImmVal(Numerical::uint(0))
                    );
                    let instr = format!(
                        "uload r{} {}\n
                         uload r{} {}\n 
                         usf r{} r{}",
                        reg_idx, sfi, reg_zero, 0, reg_idx, reg_zero 
                    );
                    self.sbuf.push_str(&instr);
                }
            }
        }
    }

    fn alloc_reg(&mut self, val: ValDat) -> usize {
        for idx in 0..self.alloced_regs.len() {
            if let Some(ValDat::None) = self.alloced_regs.get(idx) {
                self.unused_regs.push(idx);
                self.alloced_regs[idx] = val;
                return idx;
            }
        }
        let oldest = self.unused_regs.remove(0);
        let mut symbname: Option<(usize, String)> = None;

        if let Some(dat) = self.alloced_regs.get_mut(oldest) {
            self.predicted_stack.push(dat.clone());
            match dat {
                ValDat::None => {}
                ValDat::Symbol(s) => {
                    symbname = Some((s.scope, s.name.clone()));
                }
                other => {} 
            }
        }
        
        if let Some((scope, name)) = symbname {
            if let Some(val) = self.symb_table.get_mut_in_scope(&name, scope) {
                val.cur_reg = VarPosition::Stack(
                    self.predicted_stack.len().saturating_sub(1)
                );
            };
        };
        
        self.sbuf.push_str(&format!("push r{}\n", oldest));
        self.alloced_regs[oldest] = val;
        self.unused_regs.push(oldest);
        return oldest;
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
                    println!("set to none");
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
                let instrs = format!("push r1\n\
                                    push r2\n\
                                    push r3\n\
                                    movr r1 r{}\n\
                                    uload r2 2\n\
                                    xor r3 r3\n\
                                    ncall 1 r0\n\
                                    pop r3\n\
                                    pop r2\n\
                                    pop r1\n",
                reg_idx);
                self.sbuf.push_str(&instrs);
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
}

impl GenData {
    pub fn new(alloced: Vec<usize>) -> GenData {
        GenData { alloced_regs: alloced, symbols: HashMap::new(),
            expr_type: FType::none}
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
    pub fn new(scope: usize, name: String) -> FSymbTabData {
        FSymbTabData { scope: scope, name: name }
    }
}
