//! Module that describes LIA logic.
//!
//! Note that the functions and structs that are defined.

use std::fmt;

use theories::{integer};
use smt::{Logic, SMTNode};

define_sorts_for_logic!(LIA_Sorts,
                  Int -> integer::Sorts
                 );

define_fns_for_logic!(LIA_Fn,
                      IntOps -> integer::OpCodes
                     );

define_logic!(LIA,
              LIA_Fn,
              LIA_Sorts,
              map {
                  LIA_Sorts::Int(_) => integer::OpCodes::FreeVar
              }
             );
