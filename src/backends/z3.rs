//! Struct and methods to interact with the Z3 solver.

use backends::smtlib2::SMTProc;
use std::process::{Child, Command, Stdio};

#[derive(Default)]
pub struct Z3 {
    fd: Option<Child>,
}

impl SMTProc for Z3 {
    fn init(&mut self) {
        let (cmd, args) = ("z3", &["-in", "-smt2"]);
        let child = Command::new(cmd)
                        .args(args)
                        .stdout(Stdio::piped())
                        .stdin(Stdio::piped())
                        .stderr(Stdio::piped())
                        .spawn()
                        .expect("Failed to spawn process");
        self.fd = Some(child);
    }

    fn pipe<'a>(&'a mut self) -> &'a mut Child {
        if self.fd.is_none() {
            self.init();
        }
        self.fd.as_mut().unwrap()
    }
}
