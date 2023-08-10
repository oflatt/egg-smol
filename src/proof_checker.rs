use crate::*;

pub(crate) struct ProofChecker<'a> {
    termdag: TermDag,
    // A map from a proof to the term in proves
    proven: HashMap<Term, Term>,
    egraph: &'a EGraph,
}

impl<'a> ProofChecker<'a> {
    pub(crate) fn check(proofs_to_check: Vec<Term>, termdag: TermDag, egraph: &'a EGraph) {
        let mut checker = Self {
            termdag,
            egraph,
            proven: HashMap::default(),
        };
        for proof in proofs_to_check {
            checker.check_proof(proof);
        }
    }

    pub(crate) fn check_proof(&mut self, proof: Term) -> Term {
        if let Some(existing) = self.proven.get(&proof) {
            return existing.clone();
        }
        let proof_term = match &proof {
            Term::App(op, children) => {
                if op.as_str() == self.egraph.proof_state.original_name() {
                    /*
                    TODO check this was an original term in the egraph
                    */
                    assert!(children.len() == 1);
                    self.termdag.get(children[0])
                } else if op.as_str() == self.egraph.proof_state.rule_proof_constructor() {
                    assert!(children.len() == 3);
                    self.check_rule_proof(
                        self.string_from_term(self.termdag.get(children[0])),
                        self.unpack_proof_list(self.termdag.get(children[1])),
                        self.termdag.get(children[2]),
                    );
                    self.termdag.get(children[2])
                    // TODO check the rule proof
                } else {
                    panic!("Unrecognized proof type: {}", op);
                }
            }
            _ => panic!("Proofs must be applications"),
        };

        self.proven.insert(proof, proof_term.clone());
        proof_term
    }

    fn string_from_term(&self, term: Term) -> String {
        let with_quotes = self.termdag.to_string(&term);
        assert!(with_quotes.len() >= 2);
        assert!(with_quotes.starts_with('"'));
        assert!(with_quotes.ends_with('"'));
        with_quotes[1..with_quotes.len() - 1].to_string()
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

    pub(crate) fn check_rule_proof(
        &mut self,
        name: String,
        proof_list: Vec<Term>,
        _to_prove: Term,
    ) {
        // first check proofs in proof list
        let mut term_list = vec![];

        for proof in proof_list {
            term_list.push(self.check_proof(proof));
        }

        if name.contains("-merge-fn__") {
            // TODO check merge function proofs
        } else {
            let rule = self.egraph.get_term_encoded(name.into());
            let mut current_atom = 0;
            let mut bindings = HashMap::<Symbol, Term>::default();

            let num_atoms = rule
                .body
                .iter()
                .filter(|fact| matches!(fact, NormFact::Assign(..)))
                .count();
            assert_eq!(num_atoms, term_list.len());

            for fact in &rule.body {
                let current_term = term_list[current_atom].clone();
                match fact {
                    NormFact::Assign(lhs, NormExpr::Call(op, body)) => {
                        let Term::App(term_op, targs) = current_term.clone() else {
                            panic!("Expected a call in the proof");
                        };
                        assert_eq!(
                            *op,
                            top,
                            "Expected operators to match: {} != {}",
                            &NormExpr::Call(*op, body.clone()),
                            self.termdag.to_string(&current_term)
                        );
                        assert_eq!(body.len(), targs.len());
                        for (arg, targ) in
                            body.iter().zip(targs.iter().map(|t| self.termdag.get(*t)))
                        {
                            if let Some(existing) = bindings.insert(*arg, targ.clone()) {
                                assert_eq!(existing, targ);
                            }
                        }

                        if let Some(existing) = bindings.insert(*lhs, current_term.clone()) {
                            assert_eq!(existing, current_term);
                        }

                        current_atom += 1;
                    }
                    _ => {
                        // TODO
                    }
                }
            }

            // TODO check that the to_prove
            // actually appears in the body with the given bindings
        }
    }
}
