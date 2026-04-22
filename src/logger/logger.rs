use std::{collections::HashMap, fs::{self, File}, io::{Read, SeekFrom}, sync::mpsc::{Receiver, Sender}, thread::{JoinHandle, spawn}, time::Instant};

use colored::Colorize;

use crate::{CompilationError, fcparse::fcparse::{AstNode, BinaryOp}, lexer::lexer::{Tok, Token}, seman::seman::FType};

pub struct Logger {
    errc: usize,
    warnc: usize,
    time: Instant,
    pub extrn_err: CompilationError,
    cached_files: HashMap<String, Vec<String>>, // fname -> lines 
}

impl Logger {
    pub fn new() -> Logger {
        Logger { 
            errc: 0, 
            warnc: 0, 
            time: Instant::now(), 
            extrn_err: CompilationError::Ok,
            cached_files: HashMap::new()
        }
    }

    pub fn start_timer(&mut self) {
        self.time = Instant::now();
    }

    pub fn handle_messages(&mut self, rx: Receiver<LogMessage>, tx:
        Sender<LogMessage>) {
        loop {
            match rx.recv() { 
                Ok(m) => {
                    match m.query {
                        Some(v) => {
                            match v {
                                LoggerQuery::Stop => {
                                    break;
                                }
                                LoggerQuery::Status => {
                                    tx.send(LogMessage::from_query(LoggerQuery::StatusResp(
                                        self.errc > 0
                                    )));
                                    continue;
                                }
                                other => todo!("{:?}", other)
                            }
                        }
                        _other => {}
                    }
    
                    if self.cached_files.get(&m.filename).is_none() {
                        let conts = match fs::read_to_string(&m.filename) {
                            Ok(s) => s,
                            Err(e) => {
                                eprintln!("logger: failed to read {}: {}",
                                    m.filename, e);
                                "".into()
                            }
                        };
                        if !conts.is_empty() {
                            let lines: Vec<String> = conts.split('\n')
                                .map(|st| {st.to_owned()})
                                .collect();
                            self.cached_files.insert(
                                m.filename.clone(), 
                                lines
                            );
                        }
                    }
                    self.emit(m.level, m.line, m.filename);
                }
                Err(e) => {
                    eprintln!("{}", e);
                    break;
                }
            }
        }
       
        let _ = self.finalize();
        let mut resp = LogMessage::new(
            LogLevel::Info("".to_owned()), 
            0, 
            "".to_owned()
        );
        resp.brk = self.errc > 0;

        let _res = tx.send(resp);
    }

    pub fn emit(&mut self, l: LogLevel, line: usize, fname: String) {
        let (line_contents, caret_start, caret_reps) = {
            match self.cached_files.get(&fname) {
                Some(ls) => {
                    let res = ls.get(line.saturating_sub(1))
                        .cloned()
                        .unwrap_or("(failed to get this line)".to_owned());

                    let mut rep_start = 1;
                    let mut rep_count = 0;            
        
                    for ch in res.chars() {
                        match ch {
                            ' ' => {rep_start += 1;}
                            '\t' => {rep_start += 2;} // 4tab is healthier but 
                                                      // we need to fit into terminals
                            other => {break;}
                        }
                    }
                    rep_count = res.len().saturating_sub(rep_start);
                    (res, rep_start, rep_count)
                },
                None => ("(failed to open file)".into(), 0, 0)
            }
        };

        match l {
            LogLevel::Error(ek) => {
                println!("{} at line {}: {}", 
                    "ERROR".red(), line, 
                    Logger::get_err_msg(LogLevel::Error(ek))
                );
                
                println!("-> {}:", fname);
                println!("| {}\n|{}{}", 
                    line_contents, 
                    " ".repeat(caret_start),
                    "^".repeat(caret_reps)
                );
                
                self.errc += 1;
            }
            LogLevel::Warning(wk) => {
                println!("{} at line {}: {}", "Warning".yellow(), line, 
                    Logger::get_err_msg(LogLevel::Warning(wk)));
                
                println!("-> {}:", fname);
                println!("| {}\n|{}{}", 
                    line_contents, 
                    " ".repeat(caret_start),
                    "^".repeat(caret_reps)
                );

                self.warnc += 1;
            }
            LogLevel::Info(s) => {
                println!("{}: {}", "Info".bright_blue(), 
                    Logger::get_err_msg(LogLevel::Info(s)));
            }
        } 
    }

    /// prints error count message
    pub fn finalize(&self) -> Result<(), ()> {
        if self.errc > 0 {
            println!("\nCompilation {} with {} errors and {} warnings, took {:.2}s.",
                "failed".red(), self.errc, self.warnc, self.time.elapsed().as_secs_f64());
            Err(())
        } else if self.warnc > 0 {
            println!("\n{} with {} {}, took {:.2}s", "Compilation succeed".green(), self.warnc, 
                "warnings".yellow(), self.time.elapsed().as_secs_f64());
            Ok(())
        } else if let CompilationError::Ok = self.extrn_err {
            println!("\n{}, took {:.2}s.", "Compilation succeed".green(),
                self.time.elapsed().as_secs_f64());
            Ok(())
        } else {
            println!("\nCompilation {} with external error {:?}, took {:.2}s.",
                "failed".red(), self.extrn_err, self.time.elapsed().as_secs_f64()
                );
            Err(())
        }
    }

    pub fn should_interrupt(&self) -> bool {self.errc > 0}

    fn get_err_msg(l: LogLevel) -> String {
        let help = "help".blue();
        match l {
            LogLevel::Error(ek) => {
                match ek {
                    ErrKind::Redeclaration(rdc_name) => {
                        format!("Redeclaration of variable {}", rdc_name)
                    }
                    ErrKind::MismatchedTypes(ft1, ft2) => {
                        format!("Mismatched types: expected {}, found {}", ft1, ft2)
                    }
                    ErrKind::BinOpDifTypes(bop, ft1, ft2) => {
                        format!("Binary op {:?} can't be applied to different types {} and {}\n\
                            {}: consider explicitly converting types, e.g. var${}",
                            bop, ft1, ft2, help, ft1)
                    }
                    ErrKind::BoolBounds(bop) => {
                        format!("Binary op {:?} can't be applied to a boolean value\n\
                            {}: consider converting boolean into uint, e.g. var$uint",
                        bop, help)
                    }
                    ErrKind::NegateBounds(ft) => {
                        format!("Binary op Negate can only be applied to ints and floats, not {}\n\
                            {}: consider converting value into int/float if you meant it, e.g. var$int",
                            ft, help)
                    }
                    ErrKind::UndeclaredVar(name) => {
                        format!("Usage of undeclared variable {}\n\
                            {}: perhaps you wanted to declare variable using let? E.g. let {}: int = ...;", 
                        &name, help, name)
                    }
                    ErrKind::IncompatTypes(ft1, ft2) => {
                        format!("Incompatible types: left hand statement has type {}, \
                            but the right hand is {}.\n\
                            {}: consider explicitly converting types, e.g. var${} (where applicable)",
                        ft1, ft2, help, ft1)
                    }
                    ErrKind::IfStmtNotBool(ft1) => {
                        format!("Condition is not bool, found {};\n\
                            {}: consider explicitly converting, e.g. var$bool\n\
                            {}: try using `--fpermissive` flag to avoid type pedantism",
                        ft1, help, help)
                    }
                    ErrKind::BitShiftRHSType(op, ft) => {
                        format!("Binary op {:?} requires right hand statement type to be uint or ptr, \
                            found {}.\n\
                            {}: consider explicitly converting types, e.g. var$uint",
                            op, ft, help
                    )
                    }
                    ErrKind::WhileLoopNotBool(ft) => {
                       format!("Loop condition is not bool, found {};\n\
                            {}: consider explicitly converting, e.g. var$bool or var == 1\n\
                           {}: run fencyc with `--fpermissive` flag to avoid compiler's type pedantism",
                        ft, help, help)
                    }
                    ErrKind::BreakNotLoop => {
                        format!("`break` keyword used outside loop\n\
                            {}: this keyword is intented to break loop iteration", // tryna be user friendly
                        help)
                    }
                    ErrKind::ContinueNotLoop => {
                        format!("`continue` keyword used outside loop\n\
                            {}: this keyword intented to continue loop onto next iteration",
                        help)
                    }
                    ErrKind::NoMain => {
                        format!("No function main was declared\n\
                                Program should have `main()` function\n\
                            {}: declare main and write some code in it: `func main() ...`",
                        help)
                    }
                    ErrKind::NoneTypeAssign(name, rft) => {
                        format!("Variable {} has no annotated type\n\
                            {}: right hand statement has type {}, try annotating, e.g.:\n\
                            let {}: {} = ...;",
                        &name, help, rft, &name, rft)
                    }
                    ErrKind::FuncRedecl(name, first_occ_line) => {
                        format!("Function {} was already declared \n\
                            {}: this function was defined at line {} first time \n\
                            {}: you may want to use `override` keyword",
                        name, help, first_occ_line, help) 
                    }
                    ErrKind::MuchDeclArgs(name, ctr) => {
                        format!("Function {} was declared with {} arguments, but the limit is 30\n\
                            {}: for code cleanity and technical reasons, fency doesn't support more than\
                            30 function arguments",
                        name, ctr, help)
                    } 
                    ErrKind::UndeclaredFunc(name) => {
                        format!("Call of undeclared function {}\n\
                            function {} was called/referenced but never declared",
                        &name, &name)
                    }
                    ErrKind::MuchArgsPassed(func_name, expected, got) => {
                        format!("Function {} expected {} arguments, but {} were passed\n\
                            {}: none of this function overloads takes {} arguments",
                        func_name, expected, got, help, got)
                    }
                    ErrKind::FuncArgsTypeIncompat(name) => {
                        // TODO: list overloads for help
                        format!("None of `{}` function overloads are compatible with given arguments\n\
                            {}: try converting explicitly, e.g. var$int",
                        name, help)
                    }
                    ErrKind::IncompatReturn(name, expected, got) => {
                        format!("Function {} has return type {} but {} were returned\n\
                            {}: try converting explicitly, e.g. var${}",
                        name, expected, got, help, expected)
                    }
                    ErrKind::ReturnOutOfFunc => {
                        "`return` keyword used outside of function".to_owned()
                    }
                    ErrKind::FewMains(count) => {
                        format!("Function `main()` was declared multiple times\n\
                            {}: main() function is an entry point and should be declared only once,\
                            but it was declared {} times",
                        help, count)
                    }
                    ErrKind::IncompatArrType(expected, got, idx) => {
                        format!("Array has type {}[] but {}th element is {}\n\
                            {}: consider explicitly converting where possible, e.g. (expr)${}",
                        expected, idx, got, help, expected)
                    }
                    ErrKind::ArrIdxType(arr_name, got) => {
                        format!("Array {} was indexed with type {}\n\
                            arrays has to be indexed with uint values\n\
                            {}: consider converting explicitly, e.g. {}[(expr)$uint]",
                        arr_name, got, help, arr_name)
                    }
                    ErrKind::NotPub(fname) => {
                        format!("Needed {} function overload isn't public\n\
                            {}: consider declaring it publicly, e.g. \
                            `pub {}(...) -> ... ..`",
                        fname.clone(), help, fname)
                    }
                    ErrKind::MismatchFieldsCount(expected, found) => {
                        if expected > found {
                            format!("Insufficient fields! Expected {}, found {}\n\
                                {}: this structure has {} fields",
                            expected, found, help, expected)
                        } else {
                            format!("Too much fields! Expected {}, found {}\n\
                                {}: this structure has {} fields",
                            expected, found, help, expected)
                       }
                    }
                    ErrKind::MismatchFieldsTypes(name, expected, found) => {
                        format!("Mismatched field type \n\
                            \tthe field {} has type {}, but {} was provided\n\
                            {}: consider converting types explicitly, e.g. val${}\
                                (where applicable)",
                            name, expected, found, help, expected)
                    }
                    ErrKind::UnknownStruct(name) => {
                        format!("Unknown structure: {}",
                            name)
                    }
                    ErrKind::NonStructField(found) => {
                        format!("Attempting to address field for non-struct \
                            variable\n\
                            {}: value has type {}",
                            help, found)
                    }
                    ErrKind::NoField(structn, field) => {
                        format!("Attempting to address unknown field {}\n\
                            {}: structure {} has no field {}",
                            field, help, structn, field)
                    }
                    ErrKind::NoStructAddress(opname, found) => {
                        format!("Couldn't use operation {} on type {}\n\
                            {}: this operation is only possible for structs",
                            opname, found, help)
                    }
                    ErrKind::NoReturn() => {
                        format!("Function does not have a return\n\
                            {}: add a `return val;` at the end",
                            help)
                    }
                    ErrKind::SizeofNonStruct(ft) => {
                        format!("Attempting to get size of non-struct type \
                            {}\n\
                            {}: `sizeof` is meant for getting the size of struct in bytes",
                            ft, help)
                    }
                    ErrKind::IllegalCast(from, to) => {
                        format!("Illegal cast: {} -> {}",
                            from, to)
                    }
                    ErrKind::NotPubStruct(name) => {
                        format!("Attempting to use structure type {} outside \
                        of its module; struct isn't public\n\
                        {}: consider declaring this struct as public, \
                        e.g. `pub struct {} {{..}}`",
                        name, help, name)
                    },
                    ErrKind::NotStructMethod(name, ft) => {
                        format!("Attempting to call method on non-struct type\n\
                            {}: {} has type {} but methods could only be called \
                            for structures",
                            help, name, ft)
                    }
                    ErrKind::NotPubFieldAddr(name) => {
                        format!("Attempting to address field {} which isnt public\n\
                            addressing private field possible only in `impl`\n\
                            {}: consider doing this field public, e.g. `pub {}: ..`",
                            name, help, name)
                    }
                    ErrKind::ImportNotFound(nm) => {
                        format!("Imported library {} was not found",
                            nm)
                    }
                    ErrKind::ImportNoSrc(nm, path) => {
                        format!("Library {} has no `src/` directory\n\
                        {}: library {} was found in {} but it has no subdirectory \
                        src/ for source files",
                        nm, help, nm, path)
                    }
                    ErrKind::StructNonField(astn) => {
                        format!("Expected struct field, found {:?}",
                            astn)
                    }
                    ErrKind::ParseExpectedIdt(tk) => {
                        format!("Parse error: expected identifier, found {:?}",
                            tk)
                    }
                    ErrKind::HeapOnlyStack(ft) => {
                        format!("Struct {} was marked as heap-only, but attempted to\
                        create it from stack\n\
                        {}: `{} {{..}}` creates on stack",
                        ft, help, ft)
                    }
                    ErrKind::NotBlockBody(astn) => {
                        format!("Expected code block, found {:#?}\n\
                        {}: this was expected to be code block ({{..}})",
                        astn, help)
                    }
                    ErrKind::NotFuncInImpl(astn) => {
                        format!("Struct impl may only have functions (methods),\n\
                        but {:#?} was found.",
                        astn)
                    }
                    ErrKind::MainRetIncompat(ft) => {
                        format!("Function main can return only non-float numerical \
                        values or nothing, but not {}", ft)
                    }
                    ErrKind::BitsCastErr(opname, found, possible) => {
                        format!("Type {} can't be used in {} operation\n\
                        {}: possible types for this op: {:?}",
                        found, opname, help, possible)
                    }
                    ErrKind::NonArrIndex(ft) => {
                        format!("Type {} can't be indexed\n\
                        {}: indexable types are arrays and strs",
                        ft, help)
                    }
                    ErrKind::MovedValUse(nm, ft, ln, has_clone) => {
                        if has_clone {
                            format!("Use of moved value\n\
                                {} was moved at line {}\n\
                                {}: {} implements Clone, try using it where it was moved \
                                if cost is acceptable: `{}.clone()`",
                            nm, ln, help, ft, nm
                            )
                        } else {
                            format!("Use of moved value\n\
                                {} (of structure type {}) was moved at line {}",
                            nm, ft, ln
                            )
                        }
                    }
                    ErrKind::UnknownTrait(nm) => {
                        format!("Attempting to implement unknown trait {}",
                            nm)
                    }
                    ErrKind::TraitFuncArgsLen(fnname, tname, expected, got) => {
                        format!("Function arguments length incompat\n\
                        Function {} of trait {} expects {} arguments, but {} was \
                        provided",
                        fnname, tname, expected, got)
                    }
                    ErrKind::TraitUnknownFunc(fnname, tname) => {
                        format!("Unexpected function {} in trait implementation\n\
                        {}: trait {} doesn't require function {}\n\
                        {}: if you need this function, consider extracting it into\
                        normal impl or add it to trait",
                        fnname, help, tname, fnname, help)
                    }
                    ErrKind::TraitFuncArgsIncompat(fnname, tname, expected, got) => {
                        format!("Trait implementation function args incompat\n\
                        function {} of trait {} expects {} at this pos, but {} was found",
                        fnname, tname, expected, got)
                    }
                    ErrKind::TraitIncompleteImpl(tname, funcs) => {
                        format!("Trait implementaion is incomplete\n\
                        trait {} also expects this functions: {:?}",
                        tname, funcs)
                    }
                    ErrKind::TraitRetTypeIncompat(fnname, tname, exp, got) => {
                        format!("Trait implementation function return type incompat\n\
                        function {} of trait {} expects to return {}, but {} was found",
                        fnname, tname, exp, got)
                    }
                    ErrKind::SupertraitBoundUnsat(stname, supername, reqname) => {
                        format!("Supertrait bound is unsatisfied\n\
                        {} requires {} to be also implemented, but {} doesn't \
                        implement it",
                        supername, reqname, stname)
                    }
                    ErrKind::GenericFuncInimpl(fnname, tname, found) => {
                        format!("Trait bound isn't satisified\n\
                        generic function {} requires trait {} to be implemented, \
                        but type {} does not implement it.",
                        fnname, tname, found)
                    }
                    ErrKind::ParseUnexpected(tok) => {
                        format!("Parse: Unexpected tok {:?}", tok)
                    }
                    ErrKind::Internal(e) => {
                        format!("Internal error: {}", e)
                    }
                }
            }
            LogLevel::Warning(wk) => {
                match wk {
                    WarnKind::IfStmtNotBool => {
                        format!("Condition is not bool;\n\
                            {}: consider explicitly converting, e.g. var$bool\n",
                        help)
                    }
                    WarnKind::WhileLoopNotBool => {
                        format!("Loop condition is not bool;\n\
                            {}: consider explicitly converting, e.g. var$bool or var == 1\n",
                        help)
                    }
                    WarnKind::ConvSame(ft) => {
                        format!("Expression was converted to the same type\n\
                            expression already has type {}\n\
                            {}: remove type convertion",
                        ft, help)
                    }
                    WarnKind::RawPtrRet(ft) => {
                        format!("Raw pointer of type `{}` was returned from function \n\
                            if it was localy allocated on stack (e.g. through s = struct {{..}};),\
                            then this return could be unsafe.\n\
                            {}: consider using heap structs for complex scenarios.",
                            ft, help
                            )
                    }
                    WarnKind::Internal => {"".to_string()}
                }
            }
            LogLevel::Info(s) => {
                s
            }
        }
    }
}

pub fn spawn_logger_thread(log_rx: Receiver<LogMessage>, resp: Sender<LogMessage>)
    -> JoinHandle<()> {
    spawn(|| {
        let mut logger = Logger::new();
        logger.start_timer();

        logger.handle_messages(log_rx, resp);
    })
}

#[derive(Debug, Clone)]
pub struct LogMessage {
    pub level: LogLevel,
    pub line: usize,
    pub filename: String,
    pub brk: bool,
    pub query: Option<LoggerQuery>,
}

impl LogMessage {
    pub fn new(lvl: LogLevel, line: usize, fname: String) -> LogMessage {
        LogMessage { 
            level: lvl, 
            line, 
            filename: fname, 
            brk: false,
            query: None
        }
    } 
    
    pub fn from_query(q: LoggerQuery) -> LogMessage {
        let mut res = Self::new(LogLevel::Info(String::new()), 0, String::new());
        res.query = Some(q.clone());
        res
    }
}

#[derive(Debug, Clone)]
pub enum LoggerQuery {
    Stop,
    Status,
    StatusResp(bool), // err or no
}

#[derive(Debug, Clone)]
pub enum LogLevel {
    Error(ErrKind),
    Warning(WarnKind),
    Info(String),
}

#[derive(Debug, Clone)]
pub enum ErrKind {
    Redeclaration(String), // var name
    MismatchedTypes(FType, FType), // expected, found
    BinOpDifTypes(BinaryOp, FType, FType),
    BoolBounds(BinaryOp), 
    NegateBounds(FType), // got type
    UndeclaredVar(String),
    IncompatTypes(FType, FType), // lhs, rhs
    IfStmtNotBool(FType), // got type
    BitShiftRHSType(BinaryOp, FType),
    WhileLoopNotBool(FType), // got
    BreakNotLoop,
    ContinueNotLoop,
    NoMain,
    NoneTypeAssign(String, FType), // name, help (rhs type)
    FuncRedecl(String, usize), // function redeclaration (name, first declaration string)
    MuchDeclArgs(String, usize), // name, got count
    UndeclaredFunc(String), // name
    MuchArgsPassed(String, usize, usize), // name, expected, got 
    FuncArgsTypeIncompat(String), // func name
    IncompatReturn(String, FType, FType), // func name, expected, got
    ReturnOutOfFunc,
    FewMains(usize), // count
    IncompatArrType(FType, FType, usize), // expected, got, idx
    ArrIdxType(String, FType), // name, got 
    Internal(String), // msg
    NotPub(String), // func name
    MismatchFieldsCount(usize, usize), // expected count, found
    MismatchFieldsTypes(String, FType, FType), // name, expected, found
    UnknownStruct(String),
    NonStructField(FType), // found type
    NoField(String, String), // struct name, field name
    NoStructAddress(String, FType), // opname, found type
    NoReturn(),
    SizeofNonStruct(FType), // found
    IllegalCast(FType, FType), // from, to
    NotPubStruct(String),
    NotStructMethod(String, FType), // name, found ftype
    NotPubFieldAddr(String),
    ImportNotFound(String), // lib name 
    ImportNoSrc(String, String), // name, path 
    HeapOnlyStack(FType),
    NotBlockBody(Box<AstNode>), // found
    NotFuncInImpl(Box<AstNode>), // found 
    MainRetIncompat(FType), // found 
    BitsCastErr(String, FType, Vec<FType>), // op name, found type, possible fts
    StructNonField(Box<AstNode>), // found 
    NonArrIndex(FType),
    MovedValUse(String, FType, usize, bool), // var name, var type, move line, has clone

    UnknownTrait(String), // name 
    TraitFuncArgsLen(String, String, usize, usize), // func name, trait name, expected, got 
    TraitUnknownFunc(String, String), // func name, trait name
    TraitFuncArgsIncompat(String, String, FType, FType), // func name, trait name, expected, got                     
    TraitIncompleteImpl(String, Vec<String>), // trait name, func names
    TraitRetTypeIncompat(String, String, FType, FType), // func name, trait name, expected, got   
    SupertraitBoundUnsat(String, String, String), // struct name, supertrait, unsatisfied trait
    GenericFuncInimpl(String, String, FType), // func name, trait name, found ftype

    ParseExpectedIdt(Tok), // tok 
    ParseUnexpected(Tok),
}

#[derive(Debug, Clone)]
pub enum WarnKind {
    Internal,
    IfStmtNotBool,
    WhileLoopNotBool,
    ConvSame(FType),
    RawPtrRet(FType),
}
