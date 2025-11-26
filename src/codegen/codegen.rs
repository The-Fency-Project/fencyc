use std::{collections::HashMap};

use crate::{fcparse::fcparse as fparse, seman::seman::{self as sem, FSymbol, FType}};// AstNode;
use fparse::AstNode;

#[derive(Debug)]
pub struct CodeGen {
    ast: Vec<AstNode>,
    cur_ast: usize,
    pub sbuf: String,
    alloced_regs: Vec<bool>,
    unused_regs: Vec<usize>, // which are unused for some time (lru)
    pub symb_table: HashMap<String, FSymbol>
}

impl CodeGen {
    pub fn new(ast: Vec<AstNode>) -> CodeGen {
        CodeGen { 
            ast: ast, 
            cur_ast: 0,
            sbuf: String::new(),
            alloced_regs: vec![false; 32],
            unused_regs: Vec::new(),
            symb_table: HashMap::new(),
        }
    }

    pub fn gen_everything(&mut self) {
        while let Some(r) = self.ast.get(self.cur_ast) {
            let gdat = self.gen_expr(r.clone());
            self.symb_table.extend(gdat.symbols);
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
                let symb = FSymbol::new(name, leftreg, ft);
                
                res.push_symb(symb);
                self.sbuf.push_str(&instr);
                self.free_reg(rightdat.alloced_regs[0]);
            }   
            AstNode::Int(iv) => {
                let reg = self.alloc_reg();
                let instr = format!("iload r{} {}\n", reg, iv);
                res.alloced_regs.push(reg);
                self.sbuf.push_str(&instr);
            },
            AstNode::Float(fv) => {
                let reg = self.alloc_reg();
                let instr = format!("fload r{} {}\n", reg, fv);
                res.alloced_regs.push(reg);
                self.sbuf.push_str(&instr);
            },
            AstNode::Uint(uv) => {
                let reg = self.alloc_reg();
                let instr = format!("uload r{} {}\n", reg, uv);
                res.alloced_regs.push(reg);
                self.sbuf.push_str(&instr);
            }
            AstNode::BinaryOp { op, left, right } => {
                let leftdat = self.gen_expr(*left);
                let rightdat = self.gen_expr(*right);

                let mut instr = String::new();
                match op {
                    fparse::BinaryOp::Add => {
                        instr = format!("iadd r{} r{}\n", 
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        ); 
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    } 
                    fparse::BinaryOp::Substract => {
                        instr = format!("isub r{} r{}\n", 
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        ); 
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    }
                    fparse::BinaryOp::Multiply => {
                        instr = format!("imul r{} r{}\n", 
                            leftdat.alloced_regs[0],
                            rightdat.alloced_regs[0],
                        ); 
                        res.alloced_regs.push(leftdat.alloced_regs[0]);
                    } 
                    fparse::BinaryOp::Divide => {
                        instr = format!("idiv r{} r{} r{}\n", 
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
                let vsymb = self.symb_table.get(&av.clone())
                    .expect(&format!("No variable {} in scope", av));
                res.alloced_regs.push(vsymb.cur_reg);
            }
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
                return format!("{}add r{} r{}", 
                    type_pref, 
                    operands.get(0).expect(exop_msg),
                    operands.get(1).expect(exop_msg)
                );
            }
            fparse::BinaryOp::Substract => {
                return format!("{}sub r{} r{}", 
                    type_pref, 
                    operands.get(0).expect(exop_msg),
                    operands.get(1).expect(exop_msg)
                );
            }
            fparse::BinaryOp::Multiply => {
                return format!("{}mul r{} r{}", 
                    type_pref, 
                    operands.get(0).expect(exop_msg),
                    operands.get(1).expect(exop_msg)
                );
            }
            fparse::BinaryOp::Divide => {
                return format!("{}div r{} r{} r{}", 
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

    fn get_typeconv(ftyp1: FType, ftyp2: FType) -> String {
        String::new()// TODO
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
