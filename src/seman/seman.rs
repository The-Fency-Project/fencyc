#[derive(Debug)]
pub struct FSymbol {
    pub name: String,
    pub cur_reg: usize,
    pub ftype: FType, 
}

impl FSymbol {
    pub fn new(n: String, reg: usize, ft: FType) -> FSymbol {
        FSymbol { name: n, cur_reg: reg, ftype: ft }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum FType {
    uint,
    int,
    float,
    bool,
    strconst,
    dsptr,
    heapptr,
    none
}
