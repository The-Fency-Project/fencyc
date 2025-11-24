use std::{fs::File, io::Write};

use crate::fcparse::fcparse as fparse;// AstNode;
use fparse::AstNode;

#[derive(Debug)]
pub struct CodeGen {
    ast: Vec<AstNode>,
    cur_ast: usize,
    pub sbuf: String,
    alloced_regs: Vec<bool>,
    unused_regs: Vec<usize>, // which are unused for some time (lru)
}

impl CodeGen {
    pub fn new(ast: Vec<AstNode>) -> CodeGen {
        CodeGen { 
            ast: ast, 
            cur_ast: 0,
            sbuf: String::new(),
            alloced_regs: vec![false; 32],
            unused_regs: Vec::new(),
        }
    }

    pub fn gen_everything(&mut self) {
        while let Some(r) = self.ast.get(self.cur_ast) {
            self.gen_expr(r.clone());
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
            // TODO: implement codegen for expressions through the AST
            AstNode::Int(iv) => {
                let reg = self.alloc_reg();
                let instr = format!("iload r{} {}\n", reg, iv);
                res.alloced_regs.push(reg);
                self.sbuf.push_str(&instr);
            },
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
            other => {
                panic!("can't generate yet");
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

    fn printintrin(&mut self, idx: usize) {
        // intrinsic for tests
        self.sbuf.push_str(&format!("movr r1 r{}\n", idx));
        self.sbuf.push_str(&format!("uload r2 2\n")); // int!
        self.sbuf.push_str(&format!("xor r3 r3\n"));
        self.sbuf.push_str(&format!("ncall 1 r0\n"));
    }
}

#[derive(Debug)]
pub struct GenData {
    alloced_regs: Vec<usize>,
}

impl GenData {
    pub fn new(alloced: Vec<usize>) -> GenData {
        GenData { alloced_regs: alloced }
    }
}
