//! Module that describes the ArrayEx Theory

use std::fmt;

use smt::SMTNode;

#[derive(Clone, Debug)]
pub enum OpCodes {
    Select,
    Store,
}

#[derive(Clone, Debug)]
pub enum ArrayVar<X, Y>
where X: fmt::Debug + fmt::Display + Clone,
      Y: fmt::Debug + fmt::Display + Clone
{
    FreeVar(String, Box<X>, Box<Y>)
}

#[derive(Clone, Debug)]
pub enum ArrayConst<X, Y> 
where X: fmt::Debug + fmt::Display + Clone,
      Y: fmt::Debug + fmt::Display + Clone
{
    Const(Box<X>, Box<Y>),
}

impl<X, Y> fmt::Display for OpCodes<X, Y>
where X: fmt::Display + fmt::Debug + Clone,
      Y: fmt::Display + fmt::Debug + Clone {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            OpCodes::Select => "select".to_owned(),
            OpCodes::Store => "store".to_owned(),
            OpCodes::FreeVar(ref s) => s.clone(),
        };
        write!(f, "{}", s)
    }
}

impl_smt_node!(OpCodes<X, Y>, define consts [OpCodes::Const(_)]);

#[derive(Clone, Debug)]
pub enum Sorts<X, Y>
    where X: fmt::Display + fmt::Debug + Clone,
          Y: fmt::Display + fmt::Debug + Clone
{
    Array(Box<X>, Box<Y>),
}

impl<X, Y> fmt::Display for Sorts<X, Y>
    where X: fmt::Display + fmt::Debug + Clone,
          Y: fmt::Display + fmt::Debug + Clone {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            Sorts::Array(ref x, ref y) => format!("(Array {} {})", x, y),
        };
        write!(f, "{}", s)
    }
}
