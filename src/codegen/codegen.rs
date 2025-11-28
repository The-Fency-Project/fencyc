use std::{collections::HashMap};

use crate::{fcparse::fcparse::{self as fparse, AstRoot}, seman::seman::{self as sem, FSymbol, FType, SymbolTable}};// AstNode;
use fparse::AstNode;

#[derive(Debug)]
pub struct CodeGen {
    ast: Vec<AstRoot>,
    cur_ast: usize,
    pub sbuf: String,
    alloced_regs: Vec<bool>,
    unused_regs: Vec<usize>, // which are unused for some time (lru)
    pub symb_table: SymbolTable,
    stack_end: usize, // latest stack frame idx 
}

impl CodeGen {
    pub fn new(ast: Vec<AstRoot>) -> CodeGen {
        CodeGen { 
            ast: ast, 
            cur_ast: 0,
            sbuf: String::new(),
            alloced_regs: vec![false; 32],
            unused_regs: Vec::new(),
            symb_table: SymbolTable::new(),
            stack_end: 0,
        }
    }

    pub fn gen_everything(&mut self) {
        while let Some(r) = self.ast.get(self.cur_ast) {
            let gdat = self.gen_expr(r.clone().node);
            self.cur_ast += 1;
        }
        self.printintrin(0); // TODO: implement print intrinsic as  
                            // keyword and remove this
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
                
                let leftreg = self.alloc_reg();
                res.alloced_regs.push(leftreg);

                let mut instr = String::new();
                instr = format!("movr r{} r{}\n",
                        leftreg, rightdat.alloced_regs[0]);
               
                let symb = FSymbol::new(
                    name, sem::VarPosition::Register(leftreg), ft
                );
                
                self.symb_table.newsymb(symb);
                res.expr_type = ft;
                self.sbuf.push_str(&instr);
                self.free_reg(rightdat.alloced_regs[0]);
            }   
            AstNode::Int(iv) => {
                let reg = self.alloc_reg();
                let instr = format!("iload r{} {}\n", reg, iv);
                res.alloced_regs.push(reg);
                res.expr_type = FType::int;
                self.sbuf.push_str(&instr);
            },
            AstNode::Float(fv) => {
                let reg = self.alloc_reg();
                let instr = format!("fload r{} {:#?}\n", reg, fv); 
                // :#? so it would always be with point. its important for voxasm
                res.alloced_regs.push(reg);
                res.expr_type = FType::float;
                self.sbuf.push_str(&instr);
            },
            AstNode::Uint(uv) => {
                let reg = self.alloc_reg();
                let instr = format!("uload r{} {}\n", reg, uv);
                res.alloced_regs.push(reg);
                res.expr_type = FType::uint;
                self.sbuf.push_str(&instr);
            }
            AstNode::BinaryOp { op, left, right } => {
                let leftdat = self.gen_expr(*left);
                let rightdat = self.gen_expr(*right);

                let mut instr = String::new();
                let ftlet = CodeGen::ftletter(leftdat.expr_type); 
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
                    other => {
                        panic!("Unknown binary operation type: {:?}", other);
                    }
                }
                self.sbuf.push_str(&instr);
                self.free_reg(rightdat.alloced_regs[0]);
            },
            AstNode::Variable(av) => {
                let vsymb = self.symb_table.get(av.clone())
                    .expect(&format!("No variable {} in scope", av))
                    .1.clone();
                res.expr_type = vsymb.ftype;
                match vsymb.cur_reg {
                    sem::VarPosition::None => {
                        panic!("None value for {}!", vsymb.name);
                    }
                    sem::VarPosition::Register(ri) => {
                        res.alloced_regs.push(ri);
                    }
                    sem::VarPosition::Stack(sfi) => {
                        let mut instr = String::new();
                        let reg = self.alloc_reg();
                        if self.stack_end == sfi {
                            instr = format!("pop r{}\n", reg);
                        } else {
                            instr = format!(
                                "gsf r{} r{}\n",
                                reg, sfi
                            );
                        }
                        self.sbuf.push_str(&instr);
                    }
                }
            }
            AstNode::EnterScope => {
                self.symb_table.enter_scope();
            }, 
            AstNode::LeftScope => {
                let dropped = self.symb_table.exit_scope();
                for val in dropped.iter() {
                    match val {
                        sem::VarPosition::None => {}
                        sem::VarPosition::Register(ri) => {
                            self.free_reg(*ri);
                            let instr = format!("xor r{} r{}\n",
                                ri, ri);
                            self.sbuf.push_str(&instr);
                        }
                        sem::VarPosition::Stack(sfi) => {
                            let reg_idx = self.alloc_reg();
                            let reg_zero = self.alloc_reg();
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
            },
            other => {
                panic!("can't generate yet for {:?}", other);
            }
        }
        return res;
    }

    fn alloc_reg(&mut self) -> usize {
        // TODO: current algorithm could be problematic. Need upgrades.
        for idx in 0..self.alloced_regs.len() {
            if self.alloced_regs[idx] == false {
                self.unused_regs.push(idx);
                self.alloced_regs[idx] = true;
                return idx;
            }
        }
        let oldest = self.unused_regs.remove(0);
        self.sbuf.push_str(&format!("push r{}\n", oldest));

        self.unused_regs.push(oldest);
        return oldest;
    }

    fn free_reg(&mut self, idx: usize) {
        self.alloced_regs[idx] = false;
    }

    fn bop_typed(bop: fparse::BinaryOp, ftype: FType, operands: Vec<usize>, line: usize) -> String {
        let type_pref: &str = match ftype {
            FType::float => "f",
            FType::int => "i",
            other => "u",
        };
        let exop_msg = &format!("{}: expected operand", line);

        match bop {
            fparse::BinaryOp::Add => {
                return format!("{}add r{} r{}\n", 
                    type_pref, 
                    operands.get(0).expect(exop_msg),
                    operands.get(1).expect(exop_msg)
                );
            }
            fparse::BinaryOp::Substract => {
                return format!("{}sub r{} r{}\n", 
                    type_pref, 
                    operands.get(0).expect(exop_msg),
                    operands.get(1).expect(exop_msg)
                );
            }
            fparse::BinaryOp::Multiply => {
                return format!("{}mul r{} r{}\n", 
                    type_pref, 
                    operands.get(0).expect(exop_msg),
                    operands.get(1).expect(exop_msg)
                );
            }
            fparse::BinaryOp::Divide => {
                return format!("{}div r{} r{} r{}\n", 
                    type_pref, 
                    operands.get(0).expect(exop_msg),
                    operands.get(1).expect(exop_msg),
                    operands.get(2).expect(exop_msg)
                );
            }
            other => {
                panic!("{} internal error: Matching BOp for {:?} isn't implemented",
                    line, other);
            }
        }
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

    fn printintrin(&mut self, idx: usize) {
        // intrinsic for tests
        self.sbuf.push_str(&format!("movr r1 r{}\n", idx));
        self.sbuf.push_str(&format!("uload r2 2\n")); // int!
        self.sbuf.push_str(&format!("xor r3 r3\n"));
        self.sbuf.push_str(&format!("ncall 1 r0\n"));
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
