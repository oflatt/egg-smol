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
                if op.as_str() == self.egraph.proof_state.original_name() {
                    /*
                    TODO check this was an original term in the egraph
                    */
                } else if op.as_str() == self.egraph.proof_state.rule_proof_constructor() {
                    assert!(children.len() == 3);
                    self.check_rule_proof(
                        self.termdag.to_string(&self.termdag.get(children[0])),
                        self.unpack_proof_list(self.termdag.get(children[1])),
                        self.termdag.get(children[2]),
                    );
                    // TODO check the rule proof
                } else {
                    panic!("Unrecognized proof type: {}", op);
                }
            }
            _ => panic!("Proofs must be applications"),
        }

        self.proven.insert(proof);
    }

    pub(crate) fn unpack_proof_list(&self, proof_list: Term) -> Vec<Term> {
        let mut res = self.unpack_proof_list_helper(proof_list);
        res.reverse();
        res
    }

    pub(crate) fn unpack_proof_list_helper(&self, proof_list: Term) -> Vec<Term> {
        match_term_app!(proof_list; {
            (self.egraph.proof_state.proof_null_constructor(), []) => vec![],
            (self.egraph.proof_state.proof_cons_constructor(), [head, tail]) => {
                let mut res = self.unpack_proof_list_helper(self.termdag.get(*tail));
                res.push(self.termdag.get(*head));
                res
            }
        })
    }

    pub(crate) fn check_rule_proof(&self, name: String, proof_list: Vec<Term>, _to_prove: Term) {
        let rule = self.egraph.get_rule_from_rule_name(name.into());
        let current_atom = 0;
        let mut bindings = HashMap::<Symbol, Term>::default();

        // TODO check that the to_prove
        // actually appears in the body with the given bindings
    }
}
