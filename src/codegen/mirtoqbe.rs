use std::backtrace::Backtrace;

use crate::{codegen::codegen::CodeGen, mir::mir::{FBlock, FDataDef, FDataItem, FFunction, FInstr, FModule, FTerm, FTypeDef, FValue, IRBinOp, IRCmpOp, MIRTranslator}, seman::seman::FType};
use qbe::{Block as QBlock, Function as QFunction, Instr as QInstr, Linkage, Module as QModule, Type as QType, Value as QValue,
    DataDef as QDataDef, DataItem as QDataItem, TypeDef as QTypeDef, Cmp as QCmpOp};

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

    /// Not always precise for non-vars
    fn ft_from_var(val: &FValue) -> FType {
        match val {
            FValue::VarTmp(s, ft) | FValue::VarGlb(s, ft) => ft.clone(),
            FValue::UConst(_) => FType::uint,
            FValue::IConst(_) => FType::int,
            FValue::SingleConst(_) => FType::single,
            FValue::DoubleConst(_) => FType::double,
        }
    }

    fn qt_from_var(val: &FValue) -> QType {
        match val {
            FValue::VarTmp(s, ft) | FValue::VarGlb(s, ft) 
                => Self::match_ft_qbf_t(ft, true),
            FValue::UConst(_) | FValue::IConst(_) => QType::Long,
            FValue::SingleConst(s) => QType::Single,
            FValue::DoubleConst(d) => QType::Double,
        }
    }

    fn new_tmp(&mut self) -> QValue {
        let res_name = format!("qbe_tmp_{}", self.tmp_ctr);
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
                (other, FType::double) if ft_src.size(None) == target_type.size(None) => {
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
            (FType::ubyte, FType::u32) => QInstr::Extub(src),
            (FType::ibyte, FType::i32) => QInstr::Extsb(src),
            (FType::ushort, FType::u32) => QInstr::Extuh(src),
            (FType::ishort, FType::i32) => QInstr::Extsh(src),
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
            other => {
                self.emit_assign(
                    tmp.clone(),
                    Self::match_ft_qbf(cur),
                    QInstr::Copy(ogv)
                );
                return tmp;
            }
        };

        self.emit_assign(tmp.clone(), new_qt, qi);
        tmp
    }

    fn lower_expr(&mut self, expr: &FInstr, need_type: &FType) -> QValue {
        match expr {
            FInstr::Copy(ft, fv) => {
                let tmp = self.new_tmp();
                let qv = Self::transl_val(&fv);
                let qt = Self::match_ft_qbf_t(ft, true);

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
                    IRBinOp::Rem => QInstr::Rem(qv1, qv2),

                    IRBinOp::And => QInstr::And(qv1, qv2),
                    IRBinOp::Or  => QInstr::Or(qv1, qv2),
                    IRBinOp::Xor => QInstr::Xor(qv1, qv2),
                };

                self.emit_assign(tmp.clone(), qt, qinstr);
                tmp
            }
            FInstr::Cmp(cmp_op, ft, fv1, fv2) => {
                let qv1 = Self::transl_val(fv1);
                let qv2 = Self::transl_val(fv2);

                let qt = Self::match_ft_qbf(ft);
                let s  = ft.is_signed(); 

                let qop = match cmp_op {
                    IRCmpOp::Eq => QCmpOp::Eq,
                    IRCmpOp::Ne => QCmpOp::Ne,

                    IRCmpOp::Lt if s => QCmpOp::Slt,
                    IRCmpOp::Lt => QCmpOp::Ult,

                    IRCmpOp::Le if s => QCmpOp::Sle,
                    IRCmpOp::Le => QCmpOp::Ule,

                    IRCmpOp::Gt if s => QCmpOp::Sgt,
                    IRCmpOp::Gt => QCmpOp::Ugt,

                    IRCmpOp::Ge if s => QCmpOp::Sge,
                    IRCmpOp::Ge => QCmpOp::Uge,

                    other => todo!("{:?}", other)
                };

                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(), 
                    qt.clone(), 
                    QInstr::Cmp(qt, qop, qv1, qv2)
                );
                tmp
            }
            FInstr::Call(nm, args) => {
                let qargs: Vec<(QType, QValue)> = args.iter()
                    .map(|(fv, ft)| (
                        Self::match_ft_qbf_t(ft, true),
                        Self::transl_val(fv)
                    ))
                    .collect();

                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(),
                    Self::match_ft_qbf(need_type),
                    QInstr::Call(
                        nm.clone(), 
                        qargs,
                        None // TODO: va args?
                    )
                );
                tmp
            }
            FInstr::Neg(fv) => {
                let qv = Self::transl_val(fv);
                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(), 
                    Self::match_ft_qbf_t(need_type, true), 
                    QInstr::Neg(qv)
                );
                tmp
            }
            FInstr::Alloca(align, ct) => {
                let instr = match align {
                    4 => QInstr::Alloc4(*ct as u32),
                    8 => QInstr::Alloc8(*ct),
                    16 => QInstr::Alloc16(*ct as u128),
                    other => unimplemented!("Only 4/8/16 byte aligned areas could be \
                    allocated in QBE, but found {other}")
                };

                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(),
                    QType::Long,
                    instr
                );
                tmp
            }
            FInstr::Load(fv, ft) => {
                let qv = Self::transl_val(fv);
                let qt = match ft {
                    FType::none => Self::match_ft_qbf_t(need_type, false),
                    other => Self::match_ft_qbf_t(other, false),
                };

                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(), 
                    qt.clone(), 
                    QInstr::Load(qt, qv)
                );

                tmp
            }
            FInstr::GetAddr(fv_base, fv_offset) => {
                let qv_base   = Self::transl_val(fv_base);
                let qv_offset = Self::transl_val(fv_offset);
                
                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(),
                    QType::Long,
                    QInstr::Add(qv_base, qv_offset)
                );
                tmp
            }
            FInstr::Cast(fv, ft_from, ft_to) => {
                let qv = Self::transl_val(fv);
                
                let ft_to = &Self::border_ft(ft_to);

                let qt_to = Self::match_ft_qbf_t(ft_to, false);

                let cast_instr = Self::get_conv(ft_from, ft_to, qv.clone());
                
                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(),
                    qt_to.clone(),
                    cast_instr
                );
                tmp
            }
            FInstr::ReinterpretBits(fv, ft_from, ft_to) => {
                let qv = Self::transl_val(fv);

                let ft_to = &Self::border_ft(ft_to);

                match (ft_from, ft_to) {
                    other if other.0.size(None) == other.1.size(None) => {} 
                    other => unimplemented!("Reinterpret bits {} -> {}",
                        other.0, other.1)
                }

                let qt_to = Self::match_ft_qbf_t(ft_to, false);
                
                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(),
                    qt_to.clone(),
                    QInstr::Cast(qv)
                );
                tmp
            }
            other => panic!("Attempted to get value from instr {}", expr)
        }
    }

    fn border_ft(ft: &FType) -> FType {
        match ft {
            FType::ubyte | FType::ushort => FType::u32,
            FType::ibyte | FType::ishort => FType::i32,
            other => other.clone(),
        }
    }

    fn fdi_to_qdi(fdi: &FDataItem) -> QDataItem {
        match fdi {
            FDataItem::Str(s) => QDataItem::Str(s.clone()),
            FDataItem::Zeroes(c) => QDataItem::Zero(*c as u64)
        }
    }

    fn translate_datadef(&mut self, fddef: &FDataDef) -> QDataDef {
        let linkage = match fddef.public {
            true => Linkage::public(),
            false => Linkage::private()
        };

        let mut qitems: Vec<(QType, QDataItem)> = fddef.items.iter()
            .map(|(fdi, ft)| (
                match (ft, &fdi) {
                    (FType::strconst, _) => QType::Byte,
                    (_, FDataItem::Zeroes(_)) => QType::Zero,
                    other => Self::qtype_lose_sign(Self::match_ft_qbf_t(ft, true)),
                },
                Self::fdi_to_qdi(fdi)
            ))
            .collect();

        QDataDef {
            linkage,
            name: fddef.name.clone(),
            align: fddef.align,
            items: qitems,
        }
    }

    fn translate_typedef(&mut self, ftd: &FTypeDef) -> QTypeDef {
        let qitems: Vec<(QType, usize)> = ftd.items.iter()
            .map(|(ft, ct)| (
                Self::qtype_lose_sign(Self::match_ft_qbf_t(ft, true)),
                *ct
            ))
            .collect();

        QTypeDef {
            name:  ftd.name.clone(),
            align: ftd.align,
            items: qitems,
        }
    }

    pub fn match_ft_qbf(ft: &FType) -> QType {
        Self::match_ft_qbf_t(ft, false) 
    }

    /// t - true conversion 
    /// l - lose sign 
    pub fn match_ft_qbf_tl(ft: &FType, t: bool, l: bool) -> QType { 
        let mut res = Self::match_ft_qbf_t(ft, t);
        if l {
            res = Self::qtype_lose_sign(res);
        }
        res
    }

    pub fn match_ft_qbf_t(ft: &FType, straight: bool) -> QType {
        match ft {
            FType::int | FType::uint  => QType::Long,
            FType::double             => QType::Double,
            FType::single             => QType::Single,
            FType::u32 | FType::i32   => QType::Word,
            FType::Array(el, _)    => {
                Self::match_ft_qbf(
                    &*el
                )
            },
            FType::strconst | FType::StructPtr(_)
                | FType::StructHeapPtr(_) | FType::Ptr => QType::Long, // ptr 
            FType::bool | FType::ubyte if straight 
                => QType::UnsignedByte,
            FType::ibyte if straight => QType::SignedByte,
            FType::bool | FType::ubyte | FType::ibyte => QType::Word,

            FType::ushort if straight => QType::UnsignedHalfword,
            FType::ishort if straight => QType::SignedHalfword,
            FType::ushort | FType::ishort => QType::Word,

            FType::Struct(s) if straight => QType::Aggregate(
                QTypeDef { 
                    name: s.to_owned().replace("::", "_"), 
                    // other fields doesnt matter 
                    align: None, 
                    items: Vec::new()
                }
            ),
            FType::Struct(_s) => QType::Long,
            
            _other => todo!("Match ft qbf for {:?}", ft)
        }
    }

    pub fn qtype_lose_sign(qt: QType) -> QType {
        match qt {
            QType::SignedByte | QType::UnsignedByte => QType::Byte,
            QType::SignedHalfword | QType::UnsignedHalfword => QType::Halfword,
            other => other,
        }
    }
}

impl MIRTranslator for QBEBackend {
    type Output = QModule;

    fn translate_module(&mut self, module: &FModule) -> Self::Output {
        for i in module.funcs.iter() {
            self.translate_function(i);
        }
        self.set_func(None);

        for d in module.datadefs.iter() {
            let res = self.translate_datadef(d);
            self.module.add_data(res);
        }

        for t in module.typedefs.iter() {
            let res = self.translate_typedef(t);
            self.module.add_type(res);
        }

        std::mem::replace(&mut self.module, QModule::new())
    }

    fn translate_function(&mut self, func: &FFunction) {
        let qlinkage = match func.public {
            true => Linkage::public(),
            false => Linkage::private()
        };

        let qargs: Vec<(QType, QValue)> = func.params.iter()
            .map(|p| (
                Self::match_ft_qbf_t(&p.1, true),
                Self::transl_val(&p.0),
            ))
            .collect();

        let qret = match &func.ret_ft {
            FType::none => None,
            other => Some(Self::match_ft_qbf_t(&other, true))
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
                let qt = Self::match_ft_qbf(ft);

                let q_rhs = self.lower_expr(&**rhs, &ft); 

                let q_rhs = self.border_qtype(q_rhs, ft);

                self.emit_assign(q_lhs, qt, QInstr::Copy(q_rhs));
            }

            FInstr::Call(nm, args) => {
                let qargs: Vec<(QType, QValue)> = args.iter()
                    .map(|(fv, ft)| (
                        Self::match_ft_qbf_t(ft, true),
                        Self::transl_val(fv)
                    ))
                    .collect();

                self.emit(QInstr::Call(
                    nm.clone(), 
                    qargs,
                    None // TODO: va args?
                ));
            }

            FInstr::Store(dst, src, ft) => {
                let q_dst = Self::transl_val(dst);
                let q_src = Self::transl_val(src);

                let qt = Self::qtype_lose_sign(
                    Self::match_ft_qbf_t(ft, true)
                );

                self.emit(QInstr::Store(
                    qt, q_dst, q_src
                ));
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
                let qt = Self::match_ft_qbf(&Self::ft_from_var(cond));
                let tmp = self.new_tmp();
                self.emit_assign(
                    tmp.clone(),
                    qt.clone(),
                    QInstr::Cmp(
                        qt,
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


