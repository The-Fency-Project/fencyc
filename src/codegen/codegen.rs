use std::{fs::File, io::Write};

use crate::fcparse::fcparse::AstNode;

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
        while let Some(_) = self.ast.get(self.cur_ast) {
            self.gen_expr(self.cur_ast);
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

    fn gen_expr(&mut self, idx: usize) {
        let node = self.ast[self.cur_ast].clone();
        match node {
            // TODO: implement codegen for expressions through the AST
            AstNode::Int(iv) => {
                let reg = self.alloc_reg();
                let instr = format!("iload r{} {}\n", reg, iv);
                self.sbuf.push_str(&instr);
            }
            other => {
                panic!("can't generate yet");
            }
        }
        self.cur_ast += 1;
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
}
