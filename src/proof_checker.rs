use std::collections::VecDeque;

use crate::*;

pub(crate) struct ProofChecker<'a> {
    termdag: TermDag,
    proven: HashSet<Term>,
    egraph: &'a EGraph,
}

impl<'a> ProofChecker<'a> {
    pub(crate) fn check(proofs_to_check: Vec<Term>, termdag: TermDag, egraph: &'a EGraph) {
        let mut checker = Self {
            termdag,
            egraph,
            proven: HashSet::default(),
        };
        for proof in proofs_to_check {
            checker.check_proof(proof);
        }
    }

    pub(crate) fn check_proof(&mut self, proof: Term) {
        if self.proven.contains(&proof) {
            return;
        }
        match &proof {
            Term::App(op, children) => {
                if op.as_str().starts_with("Original") {
                    /*
                    TODO check this was an original term in the egraph
                    */
                } else if op.as_str().starts_with("Rule") {
                    // TODO check the rule proof
                } else {
                    panic!("Unrecognized proof type: {}", op);
                }
            }
            _ => panic!("Proofs must be applications"),
        }

        self.proven.insert(proof);
    }
}
