use crate::*;

pub(crate) struct ProofChecker<'a> {
    termdag: TermDag,
    // A map from a proof to the term in proves
    proven: HashMap<Term, Term>,
    egraph: &'a EGraph,
    term_encoded_rules: HashMap<Symbol, (NormRule, CommandId)>,
    globals: HashMap<Symbol, Term>,
}

impl<'a> ProofChecker<'a> {
    pub(crate) fn check(proofs_to_check: Vec<Term>, termdag: TermDag, egraph: &'a EGraph) {
        let mut term_encoded_rules = HashMap::default();
        for cmd in &egraph.term_encoded_program {
            if let NormCommand {
                command: NCommand::NormRule { name, rule, .. },
                metadata: Metadata { id },
            } = cmd
            {
                term_encoded_rules.insert(*name, (rule.clone(), *id));
            }
        }

        let mut checker = Self {
            termdag,
            egraph,
            proven: HashMap::default(),
            term_encoded_rules,
            globals: HashMap::default(),
        };

        checker.eval_globals();

        for proof in proofs_to_check {
            checker.check_proof(proof);
        }
    }

    fn eval_globals(&mut self) {
        for cmd in &self.egraph.term_encoded_program {
            if let NormCommand {
                command: NCommand::NormAction(action),
                ..
            } = cmd
            {
                self.eval_global_action(&action);
            };
        }
    }

    fn eval_global_action(&mut self, action: &NormAction) {
        match action {
            NormAction::Let(lhs, NormExpr::Call(op, body)) => {
                let body_terms = body
                    .iter()
                    .map(|v| self.globals.get(v).unwrap().clone())
                    .collect::<Vec<_>>();
                let body_term = self.termdag.make(*op, body_terms);
                assert!(self.globals.insert(*lhs, body_term).is_none());
            }
            NormAction::LetVar(lhs, rhs) => {
                let rhs_term = self.globals.get(rhs).unwrap().clone();
                assert!(self.globals.insert(*lhs, rhs_term).is_none());
            }
            NormAction::LetLit(lhs, lit) => {
                let rhs_term = Term::Lit(lit.clone());
                assert!(self.globals.insert(*lhs, rhs_term).is_none());
            }

            NormAction::Set(_, _) => {
                // TODO set up so that we can check proofs of original
            }
            NormAction::Union(_, _) => panic!("No union should exist after term encoding"),
            NormAction::Extract(..)
            | NormAction::Print(..)
            | NormAction::Delete(_)
            | NormAction::Panic(_) => (),
        }
    }

    pub(crate) fn check_proof(&mut self, proof: Term) -> Term {
        if let Some(existing) = self.proven.get(&proof) {
            return existing.clone();
        }
        let proof_term = match &proof {
            Term::App(op, children) => {
                // if this is an original proof
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

    // returns the function name, inputs, and output
    fn get_term_parts(&self, term: Term) -> (Symbol, Vec<Term>, Term) {
        let Term::App(term_wrapper, args) = term.clone() else {
                panic!("Proof term expected. Got: {:?}", term)
            };
        assert!(term_wrapper
            .as_str()
            .contains(&self.egraph.proof_state.term_func_ending()));
        let stripped = term_wrapper
            .as_str()
            .strip_suffix(&self.egraph.proof_state.term_func_ending())
            .unwrap();
        let func_type = self
            .egraph
            .proof_state
            .type_info
            .func_types
            .get::<Symbol>(&stripped.into())
            .unwrap_or_else(|| panic!("No function type for {}", stripped));
        let (inputs, output) = if func_type.is_datatype {
            // unwrap datatypes twice
            assert!(args.len() == 1);
            let unwrapped = self.termdag.get(args[0]);
            let Term::App(data_head, args) = unwrapped.clone() else {
                    panic!("Expected a datatype wrapper. Got: {}", self.termdag.to_string(&unwrapped))
                };
            assert!(data_head.as_str() == stripped);
            (
                args.iter().map(|child| self.termdag.get(*child)).collect(),
                unwrapped,
            )

            // output is the term itself
        } else {
            assert!(args.len() == func_type.input.len() + 1);
            (
                args[..args.len() - 1]
                    .iter()
                    .map(|t| self.termdag.get(*t))
                    .collect(),
                self.termdag.get(*args.last().unwrap()),
            )
        };

        (stripped.into(), inputs, output)
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
            let (rule, ctx) = self.get_term_encoded(name.into());
            let mut current_atom = 0;
            let mut bindings = HashMap::<Symbol, Term>::default();

            let num_atoms = rule
                .body
                .iter()
                .filter(|fact| matches!(fact, NormFact::Assign(..)))
                .count();
            assert_eq!(num_atoms, term_list.len());

            for fact in &rule.body {
                match fact {
                    NormFact::Assign(lhs, NormExpr::Call(op, body)) => {
                        let current_term = term_list[current_atom].clone();
                        let (name, inputs, output) = self.get_term_parts(current_term.clone());
                        assert_eq!(
                            *op,
                            name,
                            "Expected operators to match: {} != {}",
                            &NormExpr::Call(*op, body.clone()),
                            self.termdag.to_string(&current_term)
                        );
                        assert_eq!(body.len(), inputs.len());
                        for (arg, targ) in body.iter().zip(inputs) {
                            assert!(bindings.insert(*arg, targ.clone()).is_none());
                        }
                        assert!(bindings.insert(*lhs, output.clone()).is_none());

                        current_atom += 1;
                    }
                    NormFact::AssignVar(lhs, rhs) => {
                        let rhs_binding = self.globals.get(rhs).cloned().unwrap_or_else(|| {
                            bindings
                                .get(rhs)
                                .unwrap_or_else(|| panic!("Failed to get binding for {}", rhs))
                                .clone()
                        });
                        assert!(bindings.insert(*lhs, rhs_binding.clone()).is_none());
                    }
                    NormFact::Compute(lhs, NormExpr::Call(op, body)) => {
                        let body_terms = body
                            .iter()
                            .map(|v| bindings.get(v).unwrap().clone())
                            .collect::<Vec<_>>();
                        let output_term = self.do_compute(*op, body, &body_terms, *ctx);
                        assert!(bindings.insert(*lhs, output_term).is_none());
                    }
                    NormFact::AssignLit(lhs, lit) => {
                        let term = Term::Lit(lit.clone());
                        assert!(bindings.insert(*lhs, term).is_none());
                    }
                    NormFact::ConstrainEq(_, _) => {}
                }
            }

            // TODO check that the to_prove
            // actually appears in the body with the given bindings
        }
    }

    fn do_compute(&self, op: Symbol, body: &[Symbol], body_terms: &[Term], ctx: CommandId) -> Term {
        let body_values = body_terms
            .iter()
            .map(|t| match t {
                Term::Lit(lit) => self.egraph.eval_lit(lit),
                _ => panic!(
                    "Proof checker expects literals when computing primitives. Got: {} under {}",
                    self.termdag.to_string(t),
                    NormExpr::Call(op, body.to_vec())
                ),
            })
            .collect::<Vec<_>>();
        let input_types = body
            .iter()
            .map(|v| {
                self.egraph
                    .term_encoded_typeinfo
                    .as_ref()
                    .unwrap()
                    .lookup(ctx, *v)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let (primitive, output_type) = self
            .egraph
            .term_encoded_typeinfo
            .as_ref()
            .unwrap()
            .lookup_primitive(op, &input_types)
            .unwrap();
        let output = primitive.apply(&body_values, self.egraph).unwrap();
        let lit_output = output_type.load_prim(output).unwrap_or_else(|| {
            panic!(
                "Cannot convert output of primitive to literal for sort {}",
                output_type.name(),
            )
        });

        Term::Lit(lit_output)
    }

    fn get_term_encoded(&self, name: Symbol) -> &(NormRule, CommandId) {
        self.term_encoded_rules
            .get(&name)
            .unwrap_or_else(|| panic!("get_term_encoded: no rule named '{name}'"))
    }
}
