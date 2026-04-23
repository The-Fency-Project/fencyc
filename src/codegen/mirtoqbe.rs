use crate::{codegen::codegen::CodeGen, mir::mir::{FBlock, FFunction, FInstr, FModule, FTerm, FValue, IRBinOp, MIRTranslator}, seman::seman::FType};
use qbe::{Block as QBlock, Function as QFunction, Instr as QInstr, Linkage, Module as QModule, Type as QType, Value as QValue};

pub struct QBEBackend {
    module: QModule,
    cur_func: Option<QFunction>,
    cur_blk: Option<QBlock>,
    tmp_ctr: usize,
}

impl QBEBackend {
    pub fn new() -> QBEBackend {
        QBEBackend { 
            module: QModule::new(), 
            cur_func: None,
            cur_blk: None,
            tmp_ctr: 0
        }
    }

    fn emit(&mut self, instr: QInstr) {
        let f = self.cur_func.as_mut()
            .expect(&format!("Expression outside of function: {}", instr));
        f.add_instr(instr);
    }

    fn emit_assign(&mut self, lhs: QValue, qtype: QType, rhs: QInstr) {
        let f = self.cur_func.as_mut()
            .expect(&format!("Assignment outside of function:, {}", lhs));
        f.assign_instr(lhs, qtype, rhs);
    }

    fn set_func(&mut self, func: Option<QFunction>) {
        let old_func = self.cur_func.take();
        if let Some(f) = old_func {
            self.module.add_function(f);
        };
        self.cur_func = func;
    }

    fn set_blk(&mut self, blk: QBlock) {
        let blk_name = blk.label.clone();
        self.cur_blk = Some(blk);

        let f = self.cur_func.as_mut()
            .expect(&format!("Expected function, found none"));
        f.add_block(blk_name);
    }

    fn transl_val(val: &FValue) -> QValue {
        match val {
            FValue::VarTmp(s, ft) => QValue::Temporary(s.clone()),
            FValue::VarGlb(s, ft) => QValue::Global(s.clone()),
            
            FValue::UConst(u) => QValue::Const(*u),
            FValue::IConst(i) => QValue::SignConst(*i),

            FValue::SingleConst(s) => QValue::float(*s),
            FValue::DoubleConst(d) => QValue::double(*d)
        }
    }

    fn qt_from_var(val: &FValue) -> QType {
        match val {
            FValue::VarTmp(s, ft) | FValue::VarGlb(s, ft) 
                => CodeGen::match_ft_qbf_t(ft, true),
            FValue::UConst(_) | FValue::IConst(_) => QType::Long,
            FValue::SingleConst(s) => QType::Single,
            FValue::DoubleConst(d) => QType::Double,
        }
    }

    fn new_tmp(&mut self) -> QValue {
        let res_name = format!("tmp_{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        QValue::Temporary(res_name)
    }

    fn get_conv(ft_src: &FType, target_type: &FType, src: QValue) -> QInstr {
        match (ft_src, target_type) {
            (ft1, ft2) if *ft1 == *ft2 => {
                QInstr::Copy(src)
            }
            (FType::Ptr, FType::Array(_, _)) | (FType::Array(_, _), FType::Ptr) | 
                (FType::Ptr, FType::uint) => {
                QInstr::Copy(src)
            }
            (FType::StructPtr(st), FType::Ptr) | (FType::StructHeapPtr(st), 
                FType::Ptr) => {
                QInstr::Copy(src)
            }
            (FType::double, FType::uint) => { // bitwise repr
                QInstr::Dtoui(
                    src
                )
            }
            (FType::double, FType::int) => { // bitwise repr
                QInstr::Dtosi(
                    src
                )
            }
            (FType::uint, FType::double) => {
                QInstr::Ultof(
                    src
                )
            }
            (FType::int, FType::double) => {
                QInstr::Sltof(
                    src
                )
            }
            (FType::int, FType::uint) | (FType::uint, FType::int) => {
                QInstr::Copy(
                    src
                )
            }
            (FType::int, FType::bool) | (FType::uint, FType::bool) => {
                QInstr::Cmp(
                    QType::Long,
                    qbe::Cmp::Ne,
                    src,
                    QValue::Const(0)
                )
            }
            (FType::u32, FType::bool) | (FType::i32, FType::bool) => {
                QInstr::Cmp(
                    QType::Word,
                    qbe::Cmp::Ne,
                    src,
                    QValue::Const(0)
                )
            }
            (FType::u32, FType::uint) => {
                QInstr::Extuw(src)
            }
            (FType::i32, FType::int) => {
                QInstr::Extsw(src)
            }
            (FType::u32, FType::ubyte) => {
                QInstr::And(src, QValue::Const(255))
            }
            (FType::ubyte, FType::bool) | (FType::ibyte, FType::bool) => {
                QInstr::Cmp(
                    QType::Byte,
                    qbe::Cmp::Ne,
                    src,
                    QValue::Const(0)
                )
            }
            (FType::double, FType::single) => {
                QInstr::Truncd(src)
            }
            (FType::single, FType::double) => {
                QInstr::Exts(src)
            }
            (FType::single, other) | (other, FType::single) | (FType::double, other) |
                (other, FType::double) if ft_src.size() == target_type.size() => {
                QInstr::Cast(src)
            }
            (FType::ishort, FType::i32) | (FType::ishort, FType::int) => {
                QInstr::Extsh(src)
            }
            (FType::ushort, FType::u32) | (FType::ushort, FType::uint) => {
                QInstr::Extuh(src)
            }
            (FType::ubyte, FType::uint) | (FType::ibyte, FType::uint) => {
                QInstr::Extub(src)
            }
            (FType::ubyte, FType::int) | (FType::ibyte, FType::int) => {
                QInstr::Extsb(src)
            }
            _other => unimplemented!("Type conv: {:?} => {:?}",
                ft_src, target_type)
        }
    }

    /// Borders qbe type so it would be available for assignment 
    fn border_qtype(&mut self, ogv: QValue, cur: &FType) 
        -> QValue {
        
        let tmp = self.new_tmp();
        let (new_qt, qi) = match cur {
            FType::ubyte | FType::ushort 
                => (QType::Word, Self::get_conv(cur, &FType::u32, ogv)),
            FType::ibyte | FType::ishort 
                => (QType::Word, Self::get_conv(cur, &FType::i32, ogv)),
            other => {return ogv;}
        };

        self.emit_assign(tmp.clone(), new_qt, qi);
        tmp
    }

    fn lower_expr(&mut self, expr: &FInstr) -> QValue {
        match expr {
            FInstr::Copy(ft, fv) => {
                let tmp = self.new_tmp();
                let qv = Self::transl_val(&fv);
                let qt = CodeGen::match_ft_qbf_t(ft, true);

                self.emit_assign(tmp.clone(), qt, QInstr::Copy(qv));
                tmp
            }
            FInstr::BinaryOp(bop, fv1, fv2) => {
                let tmp = self.new_tmp();

                let qt = Self::qt_from_var(fv1);
                let (qv1, qv2) = (Self::transl_val(fv1), Self::transl_val(fv2));

                let qinstr = match bop {
                    IRBinOp::Add => QInstr::Add(qv1, qv2),
                    IRBinOp::Sub => QInstr::Sub(qv1, qv2),
                    IRBinOp::Mul => QInstr::Mul(qv1, qv2),
                    IRBinOp::Div => QInstr::Div(qv1, qv2),
                    IRBinOp::Rem => QInstr::Rem(qv1, qv2)
                };

                self.emit_assign(tmp.clone(), qt, qinstr);
                tmp
            }
            other => unreachable!("Value from instr {}", expr)
        }
    }
}

impl MIRTranslator for QBEBackend {
    type Output = QModule;

    fn translate_module(&mut self, module: &FModule) -> Self::Output {
        for i in module.funcs.iter().cloned() {
            self.translate_function(&i);
        }
        self.set_func(None);
        // TODO: datadefs, typedefs

        std::mem::replace(&mut self.module, QModule::new())
    }

    fn translate_function(&mut self, func: &FFunction) {
        let qlinkage = match func.public {
            true => Linkage::public(),
            false => Linkage::private()
        };

        let qargs: Vec<(QType, QValue)> = func.params.iter()
            .map(|p| (
                CodeGen::match_ft_qbf_t(&p.1, true),
                Self::transl_val(&p.0),
            ))
            .collect();

        let qret = match &func.ret_ft {
            FType::none => None,
            other => Some(CodeGen::match_ft_qbf_t(&other, true))
        };

        let res_func = QFunction::new(
            qlinkage, 
            func.name.clone(), 
            qargs, 
            qret
        );

        self.set_func(Some(res_func));

        for blk in func.blocks.iter() {
            self.translate_block(blk);
        }
    }

    fn translate_block(&mut self, block: &FBlock) {
        let qblk = QBlock {
            label: block.name.clone(),
            items: Vec::new(),
        };
        
        self.set_blk(qblk);

        for fi in block.instrs.iter() {
            self.translate_instr(fi); 
        }

        self.translate_term(&block.term);
    }

    fn translate_instr(&mut self, instr: &FInstr) {
        match instr {
            FInstr::Assign(lhs, ft, rhs) => {
                let q_lhs = Self::transl_val(&lhs);
                let qt = CodeGen::match_ft_qbf(ft);
                let q_rhs = self.lower_expr(&**rhs); 

                let q_rhs = self.border_qtype(q_rhs, ft);

                self.emit_assign(q_lhs, qt, QInstr::Copy(q_rhs));
            }
            
            other => panic!("Unexpected {} in instr translate. Maybe it should \
            be used within lower_expr?", other)
        };
    }

    fn translate_term(&mut self, term: &FTerm) {
        match term {
            FTerm::Return(v) => match v {
                Some(v) => self.emit(QInstr::Ret(
                    Some(Self::transl_val(&v))
                )),
                None => self.emit(QInstr::Ret(None))
            }
            FTerm::Jump(lbl) => self.emit(QInstr::Jmp(lbl.clone())),
            FTerm::Branch { cond, then_bl, else_bl } => {
                let cond_val = Self::transl_val(&cond);
                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(),
                    QType::Word,
                    QInstr::Cmp(
                        QType::Long,
                        qbe::Cmp::Eq,
                        cond_val.clone(),
                        QValue::Const(1))
                    );
                
                self.emit(QInstr::Jnz(tmp, then_bl.clone(), else_bl.clone()));
            }
            FTerm::none => 
                panic!("Reached none terminator; each block must end with some term"),
        };
    }
}
