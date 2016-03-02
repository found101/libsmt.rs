//! Example showing bitvector and array usage examples

// global _main
// section .text
// main:
// ; Some instructions, not really relevant for our case.

// write:
// ; Funtion epilogue and prologue skipped. Only function body.
// ; Unrelated asm is skipped for clarity of this example.
// ; Assume buf is assigned to be at rbp - 0xa.
// ; in x86_64, address of buf will be in rdi when this function is
// ; called.
// lea rax, [rbp - 0xa]
// add rax, rdi
// mov rax, rsi
// ret

extern crate libsmt;

use libsmt::smt::*;
use libsmt::ssmt::*;
use libsmt::theories::{array_ex, bitvec, core};
use libsmt::logics::qf_abv::QF_ABV;
use libsmt::logics::qf_abv;

macro_rules! bv_const {
    ($solver: ident, $i: expr, $n: expr) => { $solver.new_const(bitvec::OpCodes::Const($i, $n)) }
}

fn main() {
    let mut solver = SMTLib2::new(Solver::Z3, Some(QF_ABV));

    // Two symbolic vars corresponding to the user inputs.
    let rdi = solver.new_var(Some("rdi"), qf_abv::bv_sort(64));
    let rsi = solver.new_var(Some("rsi"), qf_abv::bv_sort(64));
    let bit_vec_arr = qf_abv::array_sort(qf_abv::bv_sort(64),
                                         qf_abv::bv_sort(64));
    let mem = solver.new_var(Some("mem"), bit_vec_arr);

    // Consts rbp and rsp.
    let _ = bv_const!(solver, 0x8000, 64);
    let rbp = bv_const!(solver, 0x9000, 64);

    let const_a = bv_const!(solver, 0xA, 64);
    let const_4 = bv_const!(solver, 0x4, 64);
    let const_badcafe = bv_const!(solver, 0xcafebabe, 64);

    let arr_const = qf_abv::array_const(qf_abv::bv_sort(64),
                                        qf_abv::bv_sort(64),
                                        bitvec::OpCodes::Const(0, 64));
    let const_mem_0 = solver.new_const(arr_const);

    solver.assert(core::OpCodes::Cmp, &[mem, const_mem_0]);

    let buf = solver.assert(bitvec::OpCodes::Bvsub, &[rbp, const_a]);
    let rax = solver.assert(bitvec::OpCodes::Bvadd, &[buf, rdi]);

    let ret_addr = solver.assert(bitvec::OpCodes::Bvadd, &[rbp, const_4]);

    let new_mem = solver.assert(array_ex::OpCodes::Store, &[mem, rax, rsi]);
    let sel = solver.assert(array_ex::OpCodes::Select, &[new_mem, ret_addr]);
    solver.assert(core::OpCodes::Cmp, &[sel, const_badcafe]);

    if let Ok(result) = solver.solve() {
        println!("{:#?}", result);
        println!("Out-Of-Bounds Write detected!");
        println!("rdi: 0x{:x}; rsi: 0x{:x}", result[&rdi], result[&rsi]);
    } else {
        println!("This program is not vulnerable to Out-Of-Bounds Write");
    }
}
