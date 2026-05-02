use crate::{codegen::codegen::CodeGen, mir::mir::{FBlock, FDataDef, FDataItem, FFunction, FFunctionKind, FInstr, FModule, FTerm, FTypeDef, FVal, FValue, IRBinOp, IRCmpOp, MIRTranslator}, seman::seman::FType};

use std::collections::HashMap;

use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel, builder::Builder, context::Context, module::Module, passes::PassBuilderOptions, targets::{FileType, InitializationConfig, Target as LTarget, TargetMachine}, types::{
        AnyType, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FloatType, IntType, PointerType, StructType
    }, values::{
        AnyValue, BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, GlobalValue, IntValue, PointerValue, ValueKind
    } 
};

pub struct LLVMBackend<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,

    cur_fn: Option<FunctionValue<'ctx>>,

    locals: HashMap<String, PointerValue<'ctx>>,

    globals: HashMap<String, GlobalValue<'ctx>>,

    struct_types: HashMap<String, StructType<'ctx>>,

    target_machine: TargetMachine,
    block_map: HashMap<String, inkwell::basic_block::BasicBlock<'ctx>>,

    alloca_builder: Option<Builder<'ctx>>,
}

impl<'ctx> LLVMBackend<'ctx> {
    pub fn new(context: &'ctx Context, module_name: &str, tgtm: TargetMachine) -> Self {
        Self {
            context,
            module: context.create_module(module_name),
            builder: context.create_builder(),
            cur_fn: None,
            locals: HashMap::new(),
            globals: HashMap::new(),
            struct_types: HashMap::new(),
            target_machine: tgtm,
            block_map: HashMap::new(),
            alloca_builder: None
        }
    }

    pub fn run_mem2reg(&self) {
        let passes: &[&str] = &[
            "mem2reg",     
            "instcombine", 
            "simplifycfg"  
        ];

        let pass_builder = PassBuilderOptions::create();
        self.module.run_passes(&passes.join(","), &self.target_machine, pass_builder)
            .expect("Failed to run passes");
    }

    pub fn emit_assembly_file(&self, path: &str) -> Result<(), String> {
        LTarget::initialize_all(&InitializationConfig::default());

        self.target_machine
            .write_to_file(&self.module, FileType::Assembly, path.as_ref())
            .map_err(|e| format!("Failed to write assembly file: {:?}", e))?;

        Ok(())
    }

    pub fn module(&self) -> &Module<'ctx> {
        &self.module
    }

    fn current_fn(&self) -> FunctionValue<'ctx> {
        self.cur_fn.expect("expected current function")
    }

    fn transl_val_name(val: &FValue) -> Option<String> {
        match &val.val {
            FVal::VarTmp(s) | FVal::VarGlb(s) => {
                Some(s.to_owned())
            },
            _ => None,
        }
    }

    fn ft_from_var(val: &FValue) -> FType {
        val.ftype.clone()
    }

    fn is_integer(ft: &FType) -> bool {
        matches!(
            ft,
            FType::bool
                | FType::ubyte
                | FType::ibyte
                | FType::ushort
                | FType::ishort
                | FType::u32
                | FType::i32
                | FType::uint
                | FType::int
        )
    }

    fn is_float(ft: &FType) -> bool {
        matches!(ft, FType::single | FType::double)
    }

    fn is_ptr_like(ft: &FType) -> bool {
        matches!(
            ft,
            FType::Ptr
                | FType::strconst
                | FType::StructPtr(_)
                | FType::StructHeapPtr(_)
                | FType::Struct(_)
        )
    }

    fn i64_ty(&self) -> IntType<'ctx> {
        self.context.i64_type()
    }

    fn bool_ty(&self) -> IntType<'ctx> {
        self.context.bool_type()
    }

    fn i8_ty(&self) -> IntType<'ctx> {
        self.context.i8_type()
    }

    fn i16_ty(&self) -> IntType<'ctx> {
        self.context.i16_type()
    }

    fn i32_ty(&self) -> IntType<'ctx> {
        self.context.i32_type()
    }

    fn f32_ty(&self) -> FloatType<'ctx> {
        self.context.f32_type()
    }

    fn f64_ty(&self) -> FloatType<'ctx> {
        self.context.f64_type()
    }

    fn ptr_ty(&self) -> PointerType<'ctx> {
        self.context.i8_type().ptr_type(AddressSpace::default())
    }

    fn llvm_type_of(&mut self, ft: &FType) -> BasicTypeEnum<'ctx> {
        match ft {
            FType::bool => self.bool_ty().into(),
            FType::ubyte | FType::ibyte => self.i8_ty().into(),
            FType::ushort | FType::ishort => self.i16_ty().into(),
            FType::u32 | FType::i32 => self.i32_ty().into(),
            FType::uint | FType::int => self.i64_ty().into(),
            FType::single => self.f32_ty().into(),
            FType::double => self.f64_ty().into(),
            FType::Ptr | FType::strconst | FType::StructPtr(_) 
                | FType::StructHeapPtr(_) | FType::Struct(_) => {
                self.ptr_ty().into()
            }
            FType::Usize => {
                let target_data = self.target_machine.get_target_data();

                self.context
                    .ptr_sized_int_type(&target_data, None)
                    .into()
            }
            FType::Array(elem, count) => {
                // let ety = self.llvm_type_of(elem);
                // ety.array_type(*count as u32).into()
                self.ptr_ty().into()
            }
            // FType::Struct(name) => {
            //     let key = name.replace("::", "_");
            //     if let Some(st) = self.struct_types.get(&key) {
            //         (*st).into()
            //     } else {
            //         let st = self.context.opaque_struct_type(&key);
            //         self.struct_types.insert(key, st);
            //         st.into()
            //     }
            // }
            FType::none => panic!("void type cannot be lowered as a first-class LLVM type"),
            other => panic!("unhandled type in llvm_type_of: {:?}", other),
        }
    }

    fn llvm_basic_type_or_panic(&mut self, ft: &FType) -> BasicTypeEnum<'ctx> {
        self.llvm_type_of(ft)
    }

    fn const_zero_for(&mut self, ft: &FType) -> BasicValueEnum<'ctx> {
        match ft {
            FType::bool => self.bool_ty().const_int(0, false).into(),
            FType::ubyte | FType::ibyte => self.i8_ty().const_zero().into(),
            FType::ushort | FType::ishort => self.i16_ty().const_zero().into(),
            FType::u32 | FType::i32 => self.i32_ty().const_zero().into(),
            FType::uint | FType::int => self.i64_ty().const_zero().into(),
            FType::single => self.f32_ty().const_float(0.0).into(),
            FType::double => self.f64_ty().const_float(0.0).into(),
            FType::Ptr | FType::strconst | FType::StructPtr(_) | FType::StructHeapPtr(_) => {
                self.ptr_ty().const_null().into()
            }
            FType::Array(elem, count) => {
                let ety = self.llvm_type_of(elem);
                ety.array_type(*count as u32).const_zero().into()
            }
            FType::Struct(name) => {
                let key = name.replace("::", "_");
                let st = if let Some(st) = self.struct_types.get(&key) {
                    *st
                } else {
                    let st = self.context.opaque_struct_type(&key);
                    self.struct_types.insert(key, st);
                    st
                };
                st.const_zero().into()
            }
            FType::none => panic!("cannot make zero for void"),
            other => panic!("unhandled const_zero_for: {:?}", other),
        }
    }

    fn entry_block_alloca(&mut self, ft: &FType, name: &str) -> PointerValue<'ctx> {
        let b = self.context.create_builder();
        let fnv = self.current_fn();
        let entry = fnv.get_first_basic_block().unwrap();

        b.position_at_end(entry);

        let ty = self.llvm_type_of(ft);
        let (size, align) = self.sizeal_ft(ft);

        let builder = self.alloca_builder.as_ref().unwrap_or(&b);

        match ft {
            FType::Struct(_) => {
                let ty = self.context.i8_type().array_type(size as u32);

                let ptr = builder.build_alloca(ty, "alloca_var").unwrap();
                
                let instr = ptr.as_instruction().unwrap();
                
                match align {
                    4 => instr.set_alignment(4).unwrap(),
                    8 => instr.set_alignment(8).unwrap(),
                    16 => instr.set_alignment(16).unwrap(),
                    other => panic!("LLVM backend: unsupported alloca alignment {other}"),
                };

                ptr
            }

            _ => {
                builder.build_alloca(ty, name).unwrap().into()
            }
        }
    }

    fn ensure_local_slot(&mut self, name: &str, ft: &FType) -> PointerValue<'ctx> {
        if let Some(p) = self.locals.get(name) {
            return *p;
        }
        let slot = self.entry_block_alloca(ft, name);
        self.locals.insert(name.to_string(), slot);
        slot
    }

    fn ensure_global(&mut self, name: &str, ft: &FType) -> GlobalValue<'ctx> {
        if let Some(g) = self.globals.get(name) {
            return *g;
        }

        let ty = self.llvm_type_of(ft);
        let gv = self.module.add_global(ty, None, name);
        gv.set_initializer(&ty.const_zero());
        self.globals.insert(name.to_string(), gv);
        gv
    }

    fn operand_value(&mut self, v: &FValue) -> (BasicValueEnum<'ctx>, FType) {
        match &v.val {
            FVal::VarTmp(name) => {
                let slot = *self
                    .locals
                    .get(name.as_str())
                    .unwrap_or_else(|| panic!("unknown local variable: {name}"));

                if matches!(v.ftype, FType::Struct(_)) {
                    return (slot.into(), v.ftype.clone());
                }

                let llvm_ty = self.llvm_basic_type_or_panic(&v.ftype);
                let loaded = self.builder
                    .build_load(llvm_ty, slot, name.as_str())
                    .expect("load local");

                (loaded, v.ftype.clone())
            }

            FVal::VarGlb(name) => {
                let gv = self.ensure_global(name, &v.ftype);
                (gv.as_pointer_value().into(), v.ftype.clone())
            }

            FVal::UConst(u) => {
                let ty = self.llvm_basic_type_or_panic(&v.ftype);
                let val = ty.into_int_type().const_int(*u, false);
                (val.into(), v.ftype.clone())
            }

            FVal::IConst(i) => {
                let ty = self.llvm_basic_type_or_panic(&v.ftype);
                let int_ty = ty.into_int_type();

                let bits = int_ty.get_bit_width();
                let mask = (1u64 << bits.saturating_sub(1)) - 1;

                let raw = (*i as u64) & mask;

                let const_val = int_ty.const_int(raw, true);
                (const_val.into(), v.ftype.clone())
            }

            FVal::SingleConst(f) => {
                let ty = self.llvm_basic_type_or_panic(&v.ftype);
                let const_val = ty.into_float_type().const_float(*f as f64);
                (const_val.into(), v.ftype.clone())
            }

            FVal::DoubleConst(f) => {
                let ty = self.llvm_basic_type_or_panic(&v.ftype);
                let const_val = ty.into_float_type().const_float(*f);
                (const_val.into(), v.ftype.clone())
            }
        }
    }

    fn operand_value_as(&mut self, v: &FValue, want: &FType) -> BasicValueEnum<'ctx> {
        let (val, from) = self.operand_value(v);
        self.cast_value(val, &from, want, "coerce")
    }

    fn cast_value(
        &mut self,
        val: BasicValueEnum<'ctx>,
        from: &FType,
        to: &FType,
        name: &str,
    ) -> BasicValueEnum<'ctx> {
        if from == to {
            return val;
        }

        let llvm_to_ty = self.llvm_type_of(to); 

        // Integer <-> integer
        if Self::is_integer(from) && Self::is_integer(to) {
            let src = val.into_int_value();
            let fb = from.size(None);
            let tb = to.size(None);

            if fb == tb {
                return src.into();
            } else if fb < tb {
                if from.is_signed() {
                    return self
                        .builder
                        .build_int_s_extend(src, llvm_to_ty.into_int_type(), name)
                        .expect("sext")
                        .into();
                } else {
                    return self
                        .builder
                        .build_int_z_extend(src, llvm_to_ty.into_int_type(), name)
                        .expect("zext")
                        .into();
                }
            } else {
                return self
                    .builder
                    .build_int_truncate(src, llvm_to_ty.into_int_type(), name)
                    .expect("trunc")
                    .into();
            }
        }

        // Float <-> float
        if Self::is_float(from) && Self::is_float(to) {
            let src = val.into_float_value();
            if from.size(None) == to.size(None) {
                return src.into();
            } else if matches!(to, FType::double) {
                return self
                    .builder
                    .build_float_ext(src, self.f64_ty(), name)
                    .expect("fpext")
                    .into();
            } else {
                return self
                    .builder
                    .build_float_trunc(src, self.f32_ty(), name)
                    .expect("fptrunc")
                    .into();
            }
        }

        // int <-> float
        if Self::is_integer(from) && Self::is_float(to) {
            let src = val.into_int_value();
            if from.is_signed() {
                if matches!(to, FType::double) {
                    return self
                        .builder
                        .build_signed_int_to_float(src, self.f64_ty(), name)
                        .expect("sitofp")
                        .into();
                }
                return self
                    .builder
                    .build_signed_int_to_float(src, self.f32_ty(), name)
                    .expect("sitofp")
                    .into();
            } else {
                if matches!(to, FType::double) {
                    return self
                        .builder
                        .build_unsigned_int_to_float(src, self.f64_ty(), name)
                        .expect("uitofp")
                        .into();
                }
                return self
                    .builder
                    .build_unsigned_int_to_float(src, self.f32_ty(), name)
                    .expect("uitofp")
                    .into();
            }
        }

        if Self::is_float(from) && Self::is_integer(to) {
            let src = val.into_float_value();
            let ty = self.llvm_type_of(to).into_int_type();
            if to.is_signed() {
                return self
                    .builder
                    .build_float_to_signed_int(src, ty, name)
                    .expect("fptosi")
                    .into();
            } else {
                return self
                    .builder
                    .build_float_to_unsigned_int(src, ty, name)
                    .expect("fptoui")
                    .into();
            }
        }

        // pointer <-> int
        if Self::is_ptr_like(from) && Self::is_integer(to) {
            let src = val.into_pointer_value();
            return self
                .builder
                .build_ptr_to_int(src, llvm_to_ty.into_int_type(), name)
                .expect("ptrtoint")
                .into();
        }

        if Self::is_integer(from) && Self::is_ptr_like(to) {
            let src = val.into_int_value();
            return self
                .builder
                .build_int_to_ptr(src, llvm_to_ty.into_pointer_type(), name)
                .expect("inttoptr")
                .into();
        }

        // pointer <-> pointer
        if (Self::is_ptr_like(from) && Self::is_ptr_like(to)) {
            let src = val.into_pointer_value();
            return self
                .builder
                .build_bit_cast(src, llvm_to_ty, name)
                .expect("bitcast ptr")
                .into();
        }

        // ptr → int
        if Self::is_ptr_like(from) && Self::is_integer(to) {
            let src = val.into_pointer_value();
            let ty = self.llvm_type_of(to).into_int_type();

            return self
                .builder
                .build_ptr_to_int(src, ty, name)
                .expect("ptrtoint")
                .into();
        }

        // int → ptr
        if Self::is_integer(from) && Self::is_ptr_like(to) {
            let src = val.into_int_value();
            let ty = self.llvm_type_of(to).into_pointer_type();

            return self
                .builder
                .build_int_to_ptr(src, ty, name)
                .expect("inttoptr")
                .into();
        }

        // same-size bitcast
        if from.size(None) == to.size(None) {
            return self
                .builder
                .build_bit_cast(val, llvm_to_ty, name)
                .expect("bitcast")
                .into();
        }

        panic!("unsupported cast: {:?} -> {:?}", from, to);
    }
    fn reinterpret_bits(
        &mut self,
        val: BasicValueEnum<'ctx>,
        from: &FType,
        to: &FType,
        name: &str,
    ) -> BasicValueEnum<'ctx> {
        if from.size(None) != to.size(None) {
            panic!("reinterpret bits requires same size: {:?} -> {:?}", from, to);
        }

        let llvm_ty = self.llvm_type_of(to);

        self.builder
            .build_bit_cast(val, llvm_ty, name)
            .expect("bitcast")
            .into()
    }

    fn to_bool(&mut self, val: BasicValueEnum<'ctx>, ft: &FType, name: &str) -> IntValue<'ctx> {
        match ft {
            FType::bool => val.into_int_value(),
            ft if Self::is_integer(ft) => {
                let src = val.into_int_value();
                self.builder
                    .build_int_compare(
                        IntPredicate::NE,
                        src,
                        src.get_type().const_zero(),
                        name,
                    )
                    .expect("icmp ne")
            }
            ft if Self::is_float(ft) => {
                let src = val.into_float_value();
                self.builder
                    .build_float_compare(
                        FloatPredicate::ONE,
                        src,
                        src.get_type().const_float(0.0),
                        name,
                    )
                    .expect("fcmp one")
            }
            ft if Self::is_ptr_like(ft) => {
                let src = val.into_pointer_value();
                self.builder
                    .build_is_not_null(src, name)
                    .expect("is not null")
            }
            other => panic!("cannot convert {:?} to bool", other),
        }
    }

    fn lower_expr(&mut self, expr: &FInstr, need_type: &FType) -> BasicValueEnum<'ctx> {
        match expr {
            FInstr::Copy(ft, fv) => {
                let (v, from) = self.operand_value(fv);
                self.cast_value(v, &from, ft, "copy")
            }

            FInstr::BinaryOp(bop, fv1, fv2) => {
                let want = if matches!(need_type, FType::none) {
                    Self::ft_from_var(fv1)
                } else {
                    need_type.clone()
                };

                let ft1 = fv1.ftype.clone();
                let ft2 = fv2.ftype.clone();
                
                if Self::is_ptr_like(&ft1) || Self::is_ptr_like(&ft2) {
                    let lhs = self.operand_value_as(fv1, &FType::int)
                        .into_int_value();
                    let rhs = self.operand_value_as(fv2, &FType::int)
                        .into_int_value();

                    let res = match bop {
                        IRBinOp::Add => self.builder.build_int_add(lhs, rhs, "ptr.add").unwrap(),
                        IRBinOp::Sub => self.builder.build_int_sub(lhs, rhs, "ptr.sub").unwrap(),
                        _ => panic!("unsupported pointer binary op: {:?}", bop),
                    };

                    return if Self::is_ptr_like(need_type) {
                        self.builder
                            .build_int_to_ptr(res, self.ptr_ty(), "ptr.cast")
                            .expect("inttoptr")
                            .into()
                    } else {
                        res.into()
                    };
                }

                let a = self.operand_value_as(fv1, &want);
                let b = self.operand_value_as(fv2, &want);


                if Self::is_float(&want) {
                    let lhs = a.into_float_value();
                    let rhs = b.into_float_value();

                    match bop {
                        IRBinOp::Add => self.builder.build_float_add(lhs, rhs, "fadd").unwrap(),
                        IRBinOp::Sub => self.builder.build_float_sub(lhs, rhs, "fsub").unwrap(),
                        IRBinOp::Mul => self.builder.build_float_mul(lhs, rhs, "fmul").unwrap(),
                        IRBinOp::Div => self.builder.build_float_div(lhs, rhs, "fdiv").unwrap(),
                        IRBinOp::Rem => self.builder.build_float_rem(lhs, rhs, "frem").unwrap(),

                        IRBinOp::And | IRBinOp::Or | IRBinOp::Xor => {
                            panic!("bitwise op on float type: {:?}", want)
                        }
                    }
                    .into()
                } else {
                    let lhs = a.into_int_value();
                    let rhs = b.into_int_value();

                    match bop {
                        IRBinOp::Add => self.builder.build_int_add(lhs, rhs, "add").unwrap().into(),
                        IRBinOp::Sub => self.builder.build_int_sub(lhs, rhs, "sub").unwrap().into(),
                        IRBinOp::Mul => self.builder.build_int_mul(lhs, rhs, "mul").unwrap().into(),
                        IRBinOp::Div => {
                            if want.is_signed() {
                                self.builder.build_int_signed_div(lhs, rhs, "sdiv").unwrap().into()
                            } else {
                                self.builder.build_int_unsigned_div(lhs, rhs, "udiv").unwrap().into()
                            }
                        }
                        IRBinOp::Rem => {
                            if want.is_signed() {
                                self.builder.build_int_signed_rem(lhs, rhs, "srem").unwrap().into()
                            } else {
                                self.builder.build_int_unsigned_rem(lhs, rhs, "urem").unwrap().into()
                            }
                        }

                        IRBinOp::And => self.builder.build_and(lhs, rhs, "and").unwrap().into(),
                        IRBinOp::Or  => self.builder.build_or(lhs, rhs, "or").unwrap().into(),
                        IRBinOp::Xor => self.builder.build_xor(lhs, rhs, "xor").unwrap().into(),
                    }
                }
            }

            FInstr::Cmp(cmp_op, ft, fv1, fv2) => {
                let a = self.operand_value_as(fv1, ft);
                let b = self.operand_value_as(fv2, ft);

                let res = if Self::is_float(ft) {
                    let lhs = a.into_float_value();
                    let rhs = b.into_float_value();

                    let pred = match cmp_op {
                        IRCmpOp::Eq => FloatPredicate::OEQ,
                        IRCmpOp::Ne => FloatPredicate::ONE,
                        IRCmpOp::Lt => FloatPredicate::OLT,
                        IRCmpOp::Le => FloatPredicate::OLE,
                        IRCmpOp::Gt => FloatPredicate::OGT,
                        IRCmpOp::Ge => FloatPredicate::OGE,
                    };

                    self.builder
                        .build_float_compare(pred, lhs, rhs, "fcmp")
                        .expect("fcmp")
                } else {
                    let lhs = a.into_int_value();
                    let rhs = b.into_int_value();

                    let pred = match cmp_op {
                        IRCmpOp::Eq => IntPredicate::EQ,
                        IRCmpOp::Ne => IntPredicate::NE,
                        IRCmpOp::Lt if ft.is_signed() => IntPredicate::SLT,
                        IRCmpOp::Lt => IntPredicate::ULT,
                        IRCmpOp::Le if ft.is_signed() => IntPredicate::SLE,
                        IRCmpOp::Le => IntPredicate::ULE,
                        IRCmpOp::Gt if ft.is_signed() => IntPredicate::SGT,
                        IRCmpOp::Gt => IntPredicate::UGT,
                        IRCmpOp::Ge if ft.is_signed() => IntPredicate::SGE,
                        IRCmpOp::Ge => IntPredicate::UGE,
                    };

                    self.builder
                        .build_int_compare(pred, lhs, rhs, "icmp")
                        .expect("icmp")
                };

                res.into()
            }

            FInstr::Neg(fv) => {
                let ft = if matches!(need_type, FType::none) {
                    Self::ft_from_var(fv)
                } else {
                    need_type.clone()
                };

                let (v, from) = self.operand_value(fv);
                let v = self.cast_value(v, &from, &ft, "neg.cast");

                if Self::is_float(&ft) {
                    let zero = self.const_zero_for(&ft).into_float_value();
                    let x = v.into_float_value();
                    self.builder.build_float_sub(zero, x, "fneg").unwrap().into()
                } else {
                    let zero = self.const_zero_for(&ft).into_int_value();
                    let x = v.into_int_value();
                    self.builder.build_int_sub(zero, x, "ineg").unwrap().into()
                }
            }

            FInstr::Call(nm, args) => {
                let callee = self
                    .module
                    .get_function(nm)
                    .unwrap_or_else(|| panic!("unknown function called: {nm}"));

                let mut llvm_args: Vec<BasicMetadataValueEnum<'ctx>> =
                    Vec::with_capacity(args.len());

                for (arg_v, arg_ft) in args {
                    let (v, from) = self.operand_value(arg_v);
                    let coerced = self.cast_value(v, &from, arg_ft, "arg.cast");
                    llvm_args.push(coerced.into());
                }

                let call = self
                    .builder
                    .build_call(callee, &llvm_args, "calltmp")
                    .expect("call");

                match call.try_as_basic_value() {
                    ValueKind::Basic(v) => {
                        let ret_ty = callee.get_type().get_return_type();

                        if ret_ty.is_none() {
                            return v; 
                        }

                        let ret_ft = self.llvm_type_to_ftype(ret_ty);

                        if matches!(need_type, FType::none) {
                            v
                        } else {
                            self.cast_value(v, &ret_ft, need_type, "call.ret.cast")
                        }
                    }

                    other => panic!(
                        "call used as an expression, but callee returns: {:?}",
                        other
                    ),
                }
            }

            FInstr::Alloca(align, ct) => {
                let ty = self.i8_ty().array_type(*ct as u32);
              
                let b = self.context.create_builder();
                let bb = self.builder.get_insert_block().unwrap();
                b.position_at_end(bb);

                let b = self.alloca_builder.as_ref().unwrap_or(&b);
                let ptr = b.build_alloca(ty, "alloca_var").unwrap();
                
                let instr = ptr.as_instruction().unwrap();
                
                match align {
                    4 => instr.set_alignment(4).unwrap(),
                    8 => instr.set_alignment(8).unwrap(),
                    16 => instr.set_alignment(16).unwrap(),
                    other => panic!("LLVM backend: unsupported alloca alignment {other}"),
                }
                
                ptr.into()
            }


            FInstr::Load(fv, ft) => {
                let (addr, _) = self.operand_value(fv);
                let ptr = addr.into_pointer_value();
                
                let llvm_ty = self.llvm_type_of(ft); 
                
                let loaded = self.builder.build_load(llvm_ty, ptr, "loadtmp").expect("load");
                
                if matches!(ft, FType::none) {
                    loaded
                } else {
                    self.cast_value(loaded, ft, need_type, "load.cast")
                }
            }


            FInstr::Store(_, _, _) => {
                panic!("Store is a statement, not an expression")
            }

            FInstr::GetAddr(base, offset) => {
                let (b, bft) = self.operand_value(base);
                let (o, oft) = self.operand_value(offset);

                let base_ptr = b.into_pointer_value();
                let idx = self.cast_value(o, &oft, &FType::int, "idx").into_int_value();

                let gep = unsafe {
                    self.builder.build_gep(
                        self.i8_ty(),
                        base_ptr,
                        &[idx],
                        "gep",
                    ).expect("gep")
                };

                return if Self::is_ptr_like(need_type) {
                    gep.into()
                } else {
                    gep.into() 
                };
            }
            // only for value structs
            FInstr::ExtractVal(base, ofs, ft) => {
                // let (b, bft) = self.operand_value(base);
                // let (o, oft) = self.operand_value(ofs);
                //
                // let base_av = b.into_struct_value();
                // let idx     = self.cast_value(o, &oft, &FType::int, "idx")
                //     .into_int_value();

                todo!("extractval")
            }
            FInstr::Cast(fv, ft_from, ft_to) => {
                let (v, src_ft) = self.operand_value(fv);
                self.cast_value(v, ft_from, ft_to, "cast")
            }

            FInstr::ReinterpretBits(fv, ft_from, ft_to) => {
                let (v, _) = self.operand_value(fv);
                self.reinterpret_bits(v, ft_from, ft_to, "reinterp")
            }
            other => unimplemented!("Lower instr {}", other)
        }
    }

    fn store_to_lhs(&mut self, lhs: &FValue, ft: &FType, rhs: BasicValueEnum<'ctx>) {
        let lhs_ft = &lhs.ftype;

        match &lhs.val {
            FVal::VarTmp(name) => {
                let slot = self.ensure_local_slot(name, lhs_ft);

                if matches!(lhs_ft, FType::Struct(_)) {
                    let src = rhs.into_pointer_value();
                    let (sz, al) = self.sizeal_ft(lhs_ft);
                    let sz_v = self.i64_ty().const_int(sz, false);

                    self.builder
                        .build_memcpy(slot, al as u32, src, al as u32, sz_v)
                        .expect("memcpy struct local");
                } else {
                    let v = self.cast_value(rhs, ft, lhs_ft, "store.cast");
                    self.builder.build_store(slot, v).expect("store local");
                }
            }

            FVal::VarGlb(name) => {
                let gv = self.ensure_global(name, lhs_ft);

                if matches!(lhs_ft, FType::Struct(_)) {
                    let src = rhs.into_pointer_value();
                    let (sz, al) = self.sizeal_ft(lhs_ft);
                    let sz_v = self.i64_ty().const_int(sz, false);

                    self.builder
                        .build_memcpy(gv.as_pointer_value(), al as u32, src, al as u32, sz_v)
                        .expect("memcpy struct global");
                } else {
                    let v = self.cast_value(rhs, ft, lhs_ft, "store.cast");
                    self.builder
                        .build_store(gv.as_pointer_value(), v)
                        .expect("store global");
                }
            }

            _ => panic!("assignment target must be a named variable/global: {:?}", lhs),
        }
    }

    fn llvm_type_to_ftype(&self, ty: Option<BasicTypeEnum<'ctx>>) -> FType {
        match ty {
            None => FType::none,

            Some(BasicTypeEnum::IntType(it)) => {
                match it.get_bit_width() {
                    1 => FType::bool,
                    8 => FType::ubyte,
                    16 => FType::ushort,
                    32 => FType::i32,   
                    64 => FType::int,
                    _ => FType::int,    // fallback
                }
            }

            Some(BasicTypeEnum::FloatType(ft)) => {
                match ft {
                    ft if ft == self.f32_ty() => FType::single,
                    _ => FType::double,
                }
            }

            Some(BasicTypeEnum::PointerType(_)) => {
                FType::Ptr
            }

            Some(BasicTypeEnum::ArrayType(at)) => {
                let elem = self.llvm_type_to_ftype(Some(at.get_element_type()));
                FType::Array(Box::new(elem), at.len() as usize)
            }

            Some(BasicTypeEnum::StructType(st)) => {
                if let Some(name_cstr) = st.get_name() {
                    if let Ok(name) = name_cstr.to_str() {
                        FType::Struct(name.to_string())
                    } else {
                        FType::any 
                    }
                } else {
                    FType::any 
                }
            }
            Some(BasicTypeEnum::VectorType(_)) | Some(BasicTypeEnum::ScalableVectorType(_)) 
                => todo!()
        }
    }

    fn create_function_type(&mut self, func: &FFunction) -> inkwell::types::FunctionType<'ctx> {
        let mut param_tys: Vec<BasicMetadataTypeEnum<'ctx>> = Vec::with_capacity(func.params.len());

        for (_v, ft) in &func.params {
            param_tys.push(self.llvm_basic_type_or_panic(ft).into());
        }

        match &func.ret_ft {
            FType::none => self.context.void_type().fn_type(&param_tys, false),
            ret => self.llvm_basic_type_or_panic(ret).fn_type(&param_tys, false),
        }
    }

    fn declare_function(&mut self, func: &FFunction) -> FunctionValue<'ctx> {
        if let Some(f) = self.module.get_function(&func.name) {
            return f;
        }

        let fn_ty = self.create_function_type(func);
        self.module.add_function(&func.name, fn_ty, None)
    }

    fn bool_value_for_term(&mut self, cond: &FValue) -> IntValue<'ctx> {
        let (v, _) = self.operand_value(cond);

        let ft = Self::ft_from_var(cond);
        let v = self.cast_value(v, &ft, &FType::bool, "cond.cast");

        self.to_bool(v, &FType::bool, "cond.bool")
    }

    /// Predefines libc functions that are used by fency intrinsics:
    /// printf, memcpy, strlen, etc 
    fn define_intrin_libc_funcs(&mut self) {
        let context = self.context;

        let i8_type = context.i8_type();
        let i32_type = context.i32_type();
        let i64_type = context.i64_type();

        let i8_ptr = context.ptr_type(AddressSpace::default());

        // printf: int printf(const char*, ...)
        if self.module.get_function("printf").is_none() {
            let printf_ty = i32_type.fn_type(
                &[i8_ptr.into()],
                true, // VARARGS
            );

            self.module.add_function("printf", printf_ty, None);
        }

        // strlen: size_t strlen(const char*)
        if self.module.get_function("strlen").is_none() {
            let strlen_ty = i64_type.fn_type(
                &[i8_ptr.into()],
                false,
            );

            self.module.add_function("strlen", strlen_ty, None);
        }

        // memcpy: void* memcpy(void*, const void*, size_t)
        if self.module.get_function("memcpy").is_none() {
            let memcpy_ty = i8_ptr.fn_type(
                &[
                    i8_ptr.into(), // dest
                    i8_ptr.into(), // src
                    i64_type.into() // size
                ],
                false,
            );

            self.module.add_function("memcpy", memcpy_ty, None);
        }
    }

    fn declare_datadefs(&mut self, module: &FModule) {
        for dd in &module.datadefs {
            let i8 = self.context.i8_type();

            let mut vals: Vec<_> = Vec::new();

            for (item, _fty) in &dd.items {
                match item {
                    FDataItem::Str(s) => {
                        for &b in s.as_bytes() {
                            vals.push(i8.const_int(b as u64, false));
                        }
                        vals.push(i8.const_int(0, false)); // null terminator
                    }

                    FDataItem::Zeroes(n) => {
                        for _ in 0..*n {
                            vals.push(i8.const_int(0, false));
                        }
                    }
                }
            }

            let ty = i8.array_type(vals.len() as u32);
            let init = i8.const_array(&vals);

            let gv = self.module.add_global(ty, None, &dd.name);
            gv.set_initializer(&init);

            if dd.public {
                gv.set_linkage(inkwell::module::Linkage::External);
            } else {
                gv.set_linkage(inkwell::module::Linkage::Private);
            }

            if let Some(align) = dd.align {
                gv.set_alignment(align as u32);
            }

            self.globals.insert(dd.name.clone(), gv);
        }
    }

    fn declare_typedefs(&mut self, module: &FModule) {
        for td in &module.typedefs {
            self.context.opaque_struct_type(&td.name);
        }

        for td in &module.typedefs {
            let st = self
                .context
                .get_struct_type(&td.name)
                .unwrap_or_else(|| panic!("struct not found: {}", td.name));

            let mut fields = Vec::new();

            for (fty, count) in &td.items {
                let llvm_ty = self.llvm_type_of(fty);

                for _ in 0..*count {
                    fields.push(llvm_ty);
                }
            }

            st.set_body(&fields, false);
        }
    }

    fn sizeal_ft(&mut self, ft: &FType) -> (u64, u64) {
        let (ptr_size, td) = {
            let td = self.target_machine.get_target_data();
            let pt_size = td.get_pointer_byte_size(None);
            (pt_size, td)
        };

        match ft {
            FType::Struct(sn) => {
                let lname = sn.replace("::", "_");
                let st = self.context.get_struct_type(&lname)
                    .expect(&format!("Expected struct {}", lname));
                let s  = td.get_store_size(&st);
                let al = td.get_preferred_alignment(&st.as_any_type_enum());
                (s, al.into())
            }
            FType::Ptr | FType::Usize => (ptr_size as u64, ptr_size as u64),
            other => (other.size(None), other.size(None))
        }
    }
}

impl<'ctx> MIRTranslator for LLVMBackend<'ctx> {
    type Output = Module<'ctx>;

    fn translate_module(&mut self, module: &FModule) -> Self::Output {
        for func in &module.funcs {
            self.declare_function(func);
        }

        self.define_intrin_libc_funcs();

        self.declare_datadefs(&module);

        self.declare_typedefs(&module);

        for func in &module.funcs {
            match &func.kind {
                FFunctionKind::Extern => {}
                other => {
                    self.translate_function(func)
                },
            }
        }
   
        self.run_mem2reg();
        if cfg!(debug_assertions) {
            println!("DBG llvm module \n{}\n", self.module.print_to_string().to_string());
        }
        self.module.clone()
    }

    fn translate_function(&mut self, func: &FFunction) {
        self.locals.clear();
        self.block_map.clear();

        let llvm_fn = self.declare_function(func);
        self.cur_fn = Some(llvm_fn);

        // forward decl 
        for blk in &func.blocks {
            let bb = self.context.append_basic_block(llvm_fn, &blk.name);
            self.block_map.insert(blk.name.clone(), bb);
        }

        let entry_name = &func.blocks[0].name;
        let entry_bb = *self.block_map.get(entry_name).unwrap();
        self.builder.position_at_end(entry_bb);
       
        
        for (idx, (fv, ft)) in func.params.iter().enumerate() {
            let param = llvm_fn
                .get_nth_param(idx as u32)
                .unwrap_or_else(|| panic!("missing function param #{idx} for {}", func.name));

            let name = Self::transl_val_name(fv)
                .unwrap_or_else(|| panic!("function param must be named: {:?}", fv));

            let slot = self.ensure_local_slot(&name, ft);

            match ft {
                FType::Struct(_) => {
                    let ptr = param.into_pointer_value();

                    let (s, a) = self.sizeal_ft(ft); // size, alignment
                    let s_v    = self.i64_ty().const_int(s, false);

                    self.builder
                        .build_memcpy(
                            slot,
                            a as u32,
                            ptr,
                            4,
                            s_v,
                        )
                        .expect("memcpy struct param");
                }

                _ => {
                    let casted = self.cast_value(param, ft, ft, "param.cast");
                    self.builder.build_store(slot, casted).expect("store param");
                }
            }
        }
        for blk in &func.blocks {
            self.translate_block(blk);
        }

        self.cur_fn = None;
        self.alloca_builder = None;
    }

    fn translate_block(&mut self, block: &FBlock) {
        let bb = *self
            .block_map
            .get(&block.name)
            .unwrap_or_else(|| panic!("unknown block label: {}", block.name));

        self.builder.position_at_end(bb);

        for (idx, instr) in block.instrs.iter().enumerate() {  
            self.translate_instr(instr);
            if self.alloca_builder.is_none() {
                let alloca_builder = self.context.create_builder();
                let instr = bb.get_last_instruction().unwrap();
                alloca_builder.position_before(&instr);
                self.alloca_builder = Some(alloca_builder);
            }
        }

        self.translate_term(&block.term);

        // on case if only term present in block
        if self.alloca_builder.is_none() {
                let alloca_builder = self.context.create_builder();
                let instr = bb.get_last_instruction().unwrap();
                alloca_builder.position_before(&instr);
                self.alloca_builder = Some(alloca_builder);
            }
    }

    fn translate_instr(&mut self, instr: &FInstr) {
        match instr {
            FInstr::Assign(lhs, ft, rhs) => {
                let result = self.lower_expr(&*rhs, ft);
                self.store_to_lhs(lhs, ft, result);
            }

            FInstr::Call(nm, args) => {
                let callee = self
                    .module
                    .get_function(nm)
                    .unwrap_or_else(|| panic!("unknown function called: {nm}"));

                let mut llvm_args: Vec<BasicMetadataValueEnum<'ctx>> =
                    Vec::with_capacity(args.len());

                for (arg_v, arg_ft) in args {
                    let (v, from) = self.operand_value(arg_v);
                    let coerced = self.cast_value(v, &from, arg_ft, "arg.cast");
                    llvm_args.push(coerced.into());
                }

                self.builder
                    .build_call(callee, &llvm_args, "callstmt")
                    .expect("call");
            }

            FInstr::Store(dst, src, ft) => {
                let (dst_v, dst_ft) = self.operand_value(dst);
                let dst_ptr = dst_v.into_pointer_value();

                let (src_v, src_from) = self.operand_value(src);
                let src_v = self.cast_value(src_v, &src_from, ft, "store.cast");

                self.builder
                    .build_store(dst_ptr, src_v)
                    .expect("store");
            }

            other => panic!(
                "unexpected instruction in translate_instr (maybe should be lowered in lower_expr?): {:?}",
                other
            ),
        }
    }

    fn translate_term(&mut self, term: &FTerm) {
        match term {
            FTerm::Return(v) => {
                match v {
                    Some(v) => {
                        let (rv, from) = self.operand_value(v);
                        let ret_ft = Self::ft_from_var(v);
                        let rv = self.cast_value(rv, &from, &ret_ft, "ret.cast");
                        self.builder.build_return(Some(&rv)).expect("ret");
                    }
                    None => {
                        self.builder.build_return(None).expect("ret void");
                    }
                }
            }

            FTerm::Jump(lbl) => {
                let bb = *self
                    .block_map
                    .get(lbl)
                    .unwrap_or_else(|| panic!("unknown jump target: {}", lbl));
                self.builder.build_unconditional_branch(bb).expect("jmp");
            }

            FTerm::Branch { cond, then_bl, else_bl } => {
                let cond_i1 = self.bool_value_for_term(cond);

                let then_bb = *self
                    .block_map
                    .get(then_bl)
                    .unwrap_or_else(|| panic!("unknown then block: {}", then_bl));

                let else_bb = *self
                    .block_map
                    .get(else_bl)
                    .unwrap_or_else(|| panic!("unknown else block: {}", else_bl));

                self.builder
                    .build_conditional_branch(cond_i1, then_bb, else_bb)
                    .expect("br");
            }

            FTerm::none => {
                panic!("reached empty terminator; every block must end in a terminator");
            }
        }
    }
}
