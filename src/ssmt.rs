//! Module that comtains SMTLib Backend Implementation.
//!
//! This backend outputs the constraints in standard smt-lib2 format. Hence,
//! any solver that supports this format maybe used to solve for constraints.

use std::process::{Child, Command, Stdio};
use std::collections::{HashMap, VecDeque};
use std::io::{Read, Write};
use std::fmt;
use regex::Regex;

use petgraph::graph::{Graph, NodeIndex};
use petgraph::EdgeDirection;

use smt::{Logic, SMTBackend, SMTError, SMTResult, Type, SMTNode};
use theories::{bitvec, core, integer};

/// Enum that contains the solvers that support SMTLib2 format.
#[derive(Debug, Clone, Copy)]
pub enum Solver {
    Z3,
}

/// Trait an actual backend solver must implement in order to be compatible with SMTLib2
pub trait SMTSolver {
    /// Return the string representation of the name of the solver.
    /// This is used to distinguish between the solver and make decisions based on their varied
    /// capabilities.
    fn name(&self) -> String;
    /// Shell command to be executed in order to invoke the solver.
    /// Note that the solver must support smtlib2 format in order to be compatible.
    /// This function should return a tuple of shell command and the arguments to be passed to it.
    fn exec_str(&self) -> (String, Vec<String>);
    /// Run the solver and keep it open for further IO.
    fn exec(&self) -> Child {
        let (cmd, args) = self.exec_str();
        Command::new(cmd)
            .args(&args)
            .stdout(Stdio::piped())
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("Failed to spawn process")
    }
}

impl SMTSolver for Solver {
    fn exec_str(&self) -> (String, Vec<String>) {
        match *self {
            Solver::Z3 => ("z3".to_owned(), vec!["-in".to_owned(), "-smt2".to_owned()]),
        }
    }

    fn name(&self) -> String {
        match *self {
            Solver::Z3 => "Z3",
        }
        .to_owned()
    }
}

#[derive(Clone, Debug)]
pub enum EdgeData {
    EdgeOrder(usize),
}

pub const RHS: usize = 1;
pub const LHS: usize = 0;

/// Solver struct that wraps the spawned sub-process.
pub struct SMTLib2<T: Logic> {
    solver: Option<Child>,
    logic: Option<T>,
    gr: Graph<T::Fns, EdgeData>,
    var_index: usize,
    var_map: HashMap<String, (NodeIndex, T::Sorts)>,
    idx_map: HashMap<NodeIndex, String>,
}

impl<L: Logic> SMTLib2<L> {
    pub fn new<T: SMTSolver>(s_type: T, logic: Option<L>) -> SMTLib2<L> {
        let mut solver = SMTLib2 {
            solver: Some(s_type.exec()),
            logic: logic,
            gr: Graph::new(),
            var_index: 0,
            var_map: HashMap::new(),
            idx_map: HashMap::new(),
        };

        // TODO: Re-enable success message.
        // solver.write("(set-option :print-success true)\n");
        solver
    }

    pub fn write<T: AsRef<str>>(&mut self, s: T) -> Result<(), String> {
        // TODO: Check for errors.
        if let Some(ref mut stdin) = self.solver.as_mut().unwrap().stdin.as_mut() {
            stdin.write(s.as_ref().as_bytes()).expect("Write to stdin failed");
            stdin.flush().expect("Failed to flush stdin");
        }
        Ok(())
    }

    pub fn read_until(&mut self, delimiter: &str) -> String {
        let mut s = String::new();
        let mut bytes_read = [0; 1];
        if let Some(ref mut solver) = self.solver.as_mut() {
            if let Some(ref mut stdout) = solver.stdout.as_mut() {
                loop {
                    let n = stdout.read(&mut bytes_read).unwrap();
                    s = format!("{}{}",
                                s,
                                String::from_utf8(bytes_read[0..n].to_vec()).unwrap());
                    if let Some(_) = s.find(delimiter) {
                        break;
                    }
                }
            }
        }
        s
    }

    pub fn read(&mut self) -> String {
        // XXX: This read may block indefinitely if there is nothing on the pipe to be
        // read. To prevent this we need a timeout mechanism after which we should
        // return with
        // an error, such as: ErrTimeout.
        // Another important point to note here is that, if the data available to read
        // is exactly
        // 2048 bytes, then this reading mechanism fails and will end up waiting to
        // read more data
        // (when none is available) indefinitely.
        let mut bytes_read = [0; 2048];
        let mut s = String::new();
        if let Some(ref mut solver) = self.solver.as_mut() {
            if let Some(ref mut stdout) = solver.stdout.as_mut() {
                loop {
                    let n = stdout.read(&mut bytes_read).unwrap();
                    s = format!("{}{}",
                                s,
                                String::from_utf8(bytes_read[0..n].to_vec()).unwrap());
                    if n < 2048 {
                        break;
                    }
                }
            }
        }
        s
    }

    // Recursive function that builds up the assertion string from the tree.
    pub fn expand_assertion(&self, ni: NodeIndex) -> String {
        let mut children = self.gr
                               .edges_directed(ni, EdgeDirection::Outgoing)
                               .map(|(other, edge)| {
                                   match *edge {
                                       EdgeData::EdgeOrder(ref i) => (other, *i),
                                   }
                               })
                               .collect::<Vec<_>>();
        children.sort_by(|x, y| (x.1).cmp(&y.1));

        let mut assertion = self.gr[ni].to_string();

        assertion = if self.gr[ni].is_fn() {
            format!("({}", assertion)
        } else {
            assertion
        };

        for node in &children {
            assertion = format!("{} {}", assertion, self.expand_assertion(node.0))
        }

        if self.gr[ni].is_fn() {
            format!("{})", assertion)
        } else {
            assertion
        }
    }

    pub fn new_const<T: Into<L::Fns>>(&mut self, cval: T) -> NodeIndex {
        self.gr.add_node(cval.into())
    }
}

impl<L: Logic> SMTBackend for SMTLib2<L> {
    type Idx = NodeIndex;
    type Logic = L;

    fn new_var<T, P>(&mut self, var_name: Option<T>, ty: P) -> Self::Idx
        where T: AsRef<str>,
              P: Into<<<Self as SMTBackend>::Logic as Logic>::Sorts>
    {
        let var_name = var_name.map(|s| s.as_ref().to_owned()).unwrap_or({
            self.var_index += 1;
            format!("X_{}", self.var_index)
        });
        let typ = ty.into();
        let idx = self.gr.add_node(Self::Logic::free_var(var_name.clone(), typ.clone()));
        self.var_map.insert(var_name.clone(), (idx, typ));
        self.idx_map.insert(idx, var_name);
        idx
    }

    fn set_logic(&mut self) {
        if self.logic.is_none() { return; }
        let logic = self.logic.unwrap().clone();
        self.write(format!("(set-logic {})\n", logic));
    }

    fn assert<T: Into<L::Fns>>(&mut self, assert: T, ops: &[Self::Idx]) -> Self::Idx {
        // TODO: Check correctness like operator arity.
        let assertion = self.gr.add_node(assert.into());
        for (i, op) in ops.iter().enumerate() {
            self.gr.add_edge(assertion, *op, EdgeData::EdgeOrder(i));
        }
        assertion
    }

    fn check_sat(&mut self) -> bool {
        // Write out all variable definitions.
        let mut decls = Vec::new();
        for (name, val) in &self.var_map {
            let ni = &val.0;
            let ty = &val.1;
            if self.gr[*ni].is_var() {
                decls.push(format!("(declare-fun {} () {})\n", name, ty));
            }
        }
        // Identify root nodes and generate the assertion strings.
        let mut assertions = Vec::new();
        for idx in self.gr.node_indices() {
            if self.gr.edges_directed(idx, EdgeDirection::Incoming).collect::<Vec<_>>().is_empty() {
                if self.gr[idx].is_fn() {
                    assertions.push(format!("(assert {})\n", self.expand_assertion(idx)));
                }
            }
        }

        for w in decls.iter().chain(assertions.iter()) {
            print!("{}", w);
            self.write(w);
        }

        self.write("(check-sat)\n".to_owned());
        if &self.read() == "sat\n" {
            true
        } else {
            false
        }
    }

    // TODO: Return type information along with the value.
    fn solve(&mut self) -> SMTResult<HashMap<Self::Idx, u64>> {
        let mut result = HashMap::new();
        if !self.check_sat() {
            return Err(SMTError::Unsat);
        }

        self.write("(get-model)\n".to_owned());
        // XXX: For some reason we need two reads here in order to get the result from
        // the SMT solver. Need to look into the reason for this. This might stop
        // working in the
        // future.
        let _ = self.read();
        let read_result = self.read();

        // Example of result from the solver:
        // (model
        //  (define-fun y () Int
        //    9)
        //  (define-fun x () Int
        //    10)
        // )
        let re = Regex::new(r"\s+\(define-fun (?P<var>[0-9a-zA-Z_]+) \(\) [(]?[ _a-zA-Z0-9]+[)]?\n\s+(?P<val>([0-9]+|#x[0-9a-f]+|#b[01]+))")
                     .unwrap();
        for caps in re.captures_iter(&read_result) {
            // Here the caps.name("val") can be a hex value, or a binary value or a decimal
            // value. We need to parse the output to a u64 accordingly.
            let val_str = caps.name("val").unwrap();
            let val = if val_str.len() > 2 && &val_str[0..2] == "#x" {
                          u64::from_str_radix(&val_str[2..], 16)
                      } else if val_str.len() > 2 && &val_str[0..2] == "#b" {
                          u64::from_str_radix(&val_str[2..], 2)
                      } else {
                          val_str.parse::<u64>()
                      }
                      .unwrap();
            let vname = caps.name("var").unwrap();
            result.insert(self.var_map[vname].0.clone(), val);
        }
        Ok(result)
    }

    fn raw_write<T: AsRef<str>>(&mut self, w: T) {
        self.write(w);
    }

    fn raw_read(&mut self) -> String {
        self.read()
    }
}

/// A trait that is to be implemented on a struct that configures and spawns an SMTBackend.
pub trait SMTInit {
    type For: SMTBackend;
    fn spawn(&self) -> Option<Self::For>;
}

/// Wrapper struct that is used to spawn an instance of Z3 and wrap it into a `SMTLib2`.
///
/// This provides a nice way to configure solvers before spawning an instance of it and a chance to
/// run commands in the solver before they are used elsewhere.
///
/// __TODO__: This has to be expanded to other solvers.
pub struct SpawnZ3;
impl SpawnZ3 {
    pub fn new() -> SpawnZ3 {
        SpawnZ3
    }
}

impl<T: Logic> SMTInit<For = SMTLib2<T>> {
    fn spawn(&self) -> Option<SMTLib2<T>> {
        Some(SMTLib2::new(Solver::Z3, None))
    }
}

#[cfg(test)]
mod test {
    use smt::*;
    use super::*;
    use theories::bitvec;
    use theories::{integer, core};
    use logics::{lia, qf_bv};

    #[test]
    fn test_z3_int() {
        let mut solver = SMTLib2::new(Solver::Z3, Some(lia::LIA));
        let x = solver.new_var(Some("X"), integer::Sorts::Int);
        let y = solver.new_var(Some("Y"), integer::Sorts::Int);
        let c = solver.new_const(integer::OpCodes::Const(10));
        solver.assert(core::OpCodes::Cmp, &[x, c]);
        solver.assert(integer::OpCodes::Gt, &[x, y]);
        let result = solver.solve().unwrap();
        assert_eq!(result[&x], 10);
        assert_eq!(result[&y], 9);
    }

    #[test]
    fn test_z3_bitvec() {
        let mut solver = SMTLib2::new(Solver::Z3, Some(qf_bv::QF_BV));
        let x = solver.new_var(Some("X"), bitvec::Sorts::BitVector(32));
        let c = solver.new_const(bitvec::OpCodes::Const(10, 32));
        let c8 = solver.new_const(bitvec::OpCodes::Const(8, 32));
        let y = solver.new_var(Some("Y"), bitvec::Sorts::BitVector(32));
        solver.assert(core::OpCodes::Cmp, &[x, c]);
        let x_xor_y = solver.assert(bitvec::OpCodes::Bvxor, &[x, y]);
        solver.assert(core::OpCodes::Cmp, &[x_xor_y, c8]);
        let result = solver.solve().unwrap();
        assert_eq!(result[&x], 10);
        assert_eq!(result[&y], 2);
    }

    #[test]
    fn test_z3_extract() {
        let mut solver = SMTLib2::new(Solver::Z3, Some(qf_bv::QF_BV));
        let x = solver.new_var(Some("X"), bitvec::Sorts::BitVector(32));
        let c4 = solver.new_const(bitvec::OpCodes::Const(0b100, 4));
        let x_31_28 = solver.assert(bitvec::OpCodes::Extract(31, 28), &[x]);
        solver.assert(core::OpCodes::Cmp, &[x_31_28, c4]);
        let result = solver.solve().unwrap();
        assert_eq!(result[&x], (0b100 << 28));
    }
}
