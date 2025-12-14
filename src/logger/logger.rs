use std::time::Instant;

use colored::Colorize;

use crate::{fcparse::fcparse::BinaryOp, seman::seman::FType};

pub struct Logger {
    errc: usize,
    warnc: usize,
    time: Instant
}

impl Logger {
    pub fn new() -> Logger {
        Logger { errc: 0, warnc: 0, time: Instant::now() }
    }

    pub fn start_timer(&mut self) {
        self.time = Instant::now();
    }

    pub fn emit(&mut self, l: LogLevel, line: usize) {
        match l {
            LogLevel::Error(ek) => {
                println!("{} at line {}: {}", "ERROR".red(), line, 
                    Logger::get_err_msg(LogLevel::Error(ek)));
                self.errc += 1;
            }
            LogLevel::Warning(wk) => {
                println!("{} at line {}: {}", "Warning".yellow(), line, 
                    Logger::get_err_msg(LogLevel::Warning(wk)));
                self.warnc += 1;
            }
        } 
    }

    /// prints error count message
    pub fn finalize(&self) {
        if self.errc > 0 {
            println!("\nCompilation {} with {} errors and {} warnings, took {:.2}s.",
                "failed".red(), self.errc, self.warnc, self.time.elapsed().as_secs_f64());
        } else if self.warnc > 0 {
            println!("\n{} with {} {}, took {:.2}s", "Compilation succeed".green(), self.warnc, 
                "warnings".yellow(), self.time.elapsed().as_secs_f64());
        } else {
            println!("\n{}, took {:.2}s.", "Compilation succeed".green(),
                self.time.elapsed().as_secs_f64());
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
                        format!("Mismatched types: expected {:?}, found {:?}", ft1, ft2)
                    }
                    ErrKind::BinOpDifTypes(bop, ft1, ft2) => {
                        format!("Binary op {:?} can't be applied to different types {:?} and {:?}\n\
                            {}: consider explicitly converting types, e.g. var${:?}",
                            bop, ft1, ft2, help, ft1)
                    }
                    ErrKind::BoolBounds(bop) => {
                        format!("Binary op {:?} can't be applied to a boolean value\n\
                            {}: consider converting boolean into uint, e.g. var$uint",
                        bop, help)
                    }
                    ErrKind::NegateBounds(ft) => {
                        format!("Binary op Negate can only be applied to ints and floats, not {:?}\n\
                            {}: consider converting value into int/float if you meant it, e.g. var$int",
                            ft, help)
                    }
                    ErrKind::UndeclaredVar(name) => {
                        format!("Usage of undeclared variable {}\n\
                            {}: perhaps you wanted to declare variable using let? E.g. let {}: int = ...;", 
                        &name, help, name)
                    }
                    ErrKind::IncompatTypes(ft1, ft2) => {
                        format!("Incompatible types: left hand statement has type {:?}, \
                            but the right hand is {:?}.\n\
                            {}: consider explicitly converting types, e.g. var${:?} (where applicable)",
                        ft1, ft2, help, ft1)
                    }
                    ErrKind::IfStmtNotBool(ft1) => {
                        format!("Condition is not bool, found {:?};\n\
                            {}: consider explicitly converting, e.g. var$bool\n\
                            {}: try using `--fpermissive` flag to avoid type pedantism",
                        ft1, help, help)
                    }
                    ErrKind::BitShiftRHSType(op, ft) => {
                        format!("Binary op {:?} requires right hand statement type to be uint or ptr, \
                            found {:?}.\n\
                            {}: consider explicitly converting types, e.g. var$uint",
                            op, ft, help
                    )
                    }
                    ErrKind::WhileLoopNotBool(ft) => {
                       format!("Loop condition is not bool, found {:?};\n\
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
                            {}: right hand statement has type {:?}, try annotating, e.g.:\n\
                            let {}: {:?} = ...;",
                        &name, help, rft, &name, rft)
                    }
                    ErrKind::FuncRedecl(name, first_occ_line) => {
                        format!("Function {} was already declared \n\
                            {}: this function was defined at line {} first time \n\
                            {}: `override` keyword will be available soon",
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
                            {}: function {} was called/referenced but never declared",
                        &name, help, &name)
                    }
                    ErrKind::MuchArgsPassed(expected, got) => {
                        format!("Function expected {} arguments, but {} were passed\n\
                            {}: this function takes {} arguments",
                        expected, got, help, expected)
                    }
                    ErrKind::FuncArgsTypeIncompat(arg_idx, expected, got) => {
                        format!("{}-th argument has type {:?} but {:?} was expected\n\
                            {}: this function's {}-th argument is {:?}",
                        arg_idx, got, expected, help, arg_idx, expected)
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
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum LogLevel {
    Error(ErrKind),
    Warning(WarnKind),
}

#[derive(Debug)]
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
    MuchArgsPassed(usize, usize), // expected, got 
    FuncArgsTypeIncompat(usize, FType, FType), // arg_idx, expected, got
}

#[derive(Debug)]
pub enum WarnKind {
    IfStmtNotBool,
    WhileLoopNotBool,
}
