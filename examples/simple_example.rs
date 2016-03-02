// A simple example to highlight the application of Z3 and interacting with it through Rust.

// Consider following set of constraints :-
// x + y > 5
// x > 1
// y > 1

// To find a satisfiable solution of x & y for above equations we can write the following SMTLIB2 syntax in Z3 :-

// ; SMTLIB2 code for above constraints
// (set-logic LIA)
// (declare-fun x () Int)
// (declare-fun y () Int)
// (assert (> (+ x y) 5))
// (assert (> x 1))
// (assert (> y 1))

// The libsmt library is designed to simplify this process of interacting with Z3 and enable to do so programmatically through Rust


// Import the libsmt library
extern crate libsmt;

use libsmt::smt::*;
use libsmt::ssmt::*;

// Include the Int theory and its functions
use libsmt::theories::{integer};

// Include the LIA logic
use libsmt::logics::lia::LIA;

fn main() {

    // Defining an instance of Z3 solver
    let mut solver = SMTLib2::new(Solver::Z3, Some(LIA));
    solver.set_logic();

    // Defining the symbolic vars x & y
    let x = solver.new_var(Some("x"),integer::Sorts::Int);
    let y = solver.new_var(Some("y"),integer::Sorts::Int);

    // Defining the integer constants
    let int5 = solver.new_const(integer::OpCodes::Const(5));
    let int1 = solver.new_const(integer::OpCodes::Const(1));

    // Defining the assert conditions
    let cond1 = solver.assert(integer::OpCodes::Add, &[x, y]);
    let cond2 = solver.assert(integer::OpCodes::Gt, &[cond1, int5]);
    let cond3 = solver.assert(integer::OpCodes::Gt, &[x, int1]); 
    let cond4 = solver.assert(integer::OpCodes::Gt, &[y, int1]);

    if let Ok(result) = solver.solve() {
        println!("x: {}; y: {}", result[&x], result[&y]);
    } else {
        println!("No solutions for x and y found for given set of constraints");
    }

}

