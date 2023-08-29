use crate::{termdag::TermId, *};

pub(crate) struct ProofChecker<'a> {
    termdag: TermDag,
    // A map from a proof to the term in proves
    proven: HashMap<Term, Term>,
    egraph: &'a EGraph,
    term_encoded_rules: HashMap<Symbol, (NormRule, CommandId)>,
    globals: HashMap<Symbol, Term>,
    global_primitives: HashMap<Symbol, Value>,
}

struct RuleContext {
    bindings: HashMap<Symbol, Term>,
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
            global_primitives: HashMap::default(),
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
                metadata: Metadata { id },
            } = cmd
            {
                self.eval_global_action(action, *id);
            };
        }
    }

    fn eval_global_action(&mut self, action: &NormAction, id: CommandId) {
        match action {
            NormAction::Let(lhs, NormExpr::Call(op, body)) => {
                let input_types = body
                    .iter()
                    .map(|v| self.egraph.term_encoded_typeinfo.lookup(id, *v).unwrap())
                    .collect::<Vec<_>>();
                let func_type = self
                    .egraph
                    .term_encoded_typeinfo
                    .lookup_func(*op, input_types)
                    .unwrap();
                if func_type.is_primitive {
                    let body_terms = body
                        .iter()
                        .map(|v| self.get_global_term(*v))
                        .collect::<Vec<_>>();
                    let term = self.termdag.make(*op, body_terms, None);
                    let (_output_value, output_term) = self.do_compute(term);
                    self.set_global_term(*lhs, output_term);
                } else {
                    let body_terms = body
                        .iter()
                        .map(|v| self.get_global_term(*v))
                        .collect::<Vec<_>>();
                    let body_term = self.termdag.make(*op, body_terms, None);
                    self.set_global_term(*lhs, body_term)
                }
            }
            NormAction::LetVar(lhs, rhs) => {
                let rhs_term = self.get_global_term(*rhs);
                self.set_global_term(*lhs, rhs_term);
                if let Some(rhs_value) = self.get_global_value(*rhs) {
                    self.set_global_value(*lhs, rhs_value)
                }
            }
            NormAction::LetLit(lhs, lit) => {
                let rhs_term = self.termdag.make_lit(lit.clone(), Some(self.egraph));
                self.set_global_term(*lhs, rhs_term)
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
                    self.termdag.get_term(children[0])
                } else if op.as_str() == self.egraph.proof_state.rule_proof_constructor() {
                    assert!(children.len() == 3);
                    self.check_rule_proof(
                        self.string_from_term(self.termdag.get_term(children[0])),
                        self.unpack_proof_list(self.termdag.get_term(children[1])),
                        self.termdag.get_term(children[2]),
                    );
                    self.termdag.get_term(children[2])
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
                let mut res = self.unpack_proof_list_helper(self.termdag.get_term(*tail));
                res.push(self.termdag.get_term(*head));
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
            let unwrapped = self.termdag.get_term(args[0]);
            let Term::App(data_head, args) = unwrapped.clone() else {
                    panic!("Expected a datatype wrapper. Got: {}", self.termdag.to_string(&unwrapped))
                };
            assert!(data_head.as_str() == stripped);
            (
                args.iter()
                    .map(|child| self.termdag.get_term(*child))
                    .collect(),
                unwrapped,
            )

            // output is the term itself
        } else {
            assert!(args.len() == func_type.input.len() + 1);
            (
                args[..args.len() - 1]
                    .iter()
                    .map(|t| self.termdag.get_term(*t))
                    .collect(),
                self.termdag.get_term(*args.last().unwrap()),
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
            let (rule, _ctx) = self.get_term_encoded(name.into()).clone();
            let mut current_atom = 0;
            let mut rule_ctx = RuleContext {
                bindings: HashMap::default(),
            };

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
                            self.set_term(&mut rule_ctx, *arg, targ);
                        }
                        self.set_term(&mut rule_ctx, *lhs, output.clone());

                        current_atom += 1;
                    }
                    NormFact::AssignVar(lhs, rhs) => {
                        let rhs_binding = self.get_term(&rule_ctx, *rhs);
                        self.set_term(&mut rule_ctx, *lhs, rhs_binding);
                    }
                    NormFact::Compute(lhs, NormExpr::Call(op, body)) => {
                        let body_terms = body
                            .iter()
                            .map(|v| self.get_term(&rule_ctx, *v))
                            .collect::<Vec<_>>();
                        let call_term = self.termdag.make(*op, body_terms.clone(), None);
                        let (_output_value, output_term) = self.do_compute(call_term);
                        self.set_term(&mut rule_ctx, *lhs, output_term);
                    }
                    NormFact::AssignLit(lhs, lit) => {
                        let term = self.termdag.make_lit(lit.clone(), Some(self.egraph));
                        self.set_term(&mut rule_ctx, *lhs, term.clone());
                    }
                    NormFact::ConstrainEq(_, _) => {}
                }
            }

            // TODO check that the to_prove
            // actually appears in the body with the given bindings
        }
    }

    fn get_global_term(&self, sym: Symbol) -> Term {
        self.globals
            .get(&sym)
            .unwrap_or_else(|| panic!("Failed to get binding for {}", sym))
            .clone()
    }

    fn set_global_term(&mut self, sym: Symbol, term: Term) {
        assert!(self.globals.insert(sym, term.clone()).is_none());
        if let Term::Lit(l) = term {
            self.global_primitives.insert(sym, self.egraph.eval_lit(&l));
        }
    }

    fn get_global_value(&self, sym: Symbol) -> Option<Value> {
        self.global_primitives.get(&sym).cloned()
    }

    fn set_global_value(&mut self, sym: Symbol, val: Value) {
        if let Some(existing) = self.global_primitives.insert(sym, val) {
            assert!(existing == val);
        }
    }

    fn get_term(&self, rule_ctx: &RuleContext, sym: Symbol) -> Term {
        rule_ctx
            .bindings
            .get(&sym)
            .unwrap_or_else(|| {
                self.globals
                    .get(&sym)
                    .unwrap_or_else(|| panic!("Failed to get binding for {}", sym))
            })
            .clone()
    }

    fn set_term(&mut self, rule_ctx: &mut RuleContext, sym: Symbol, term: Term) {
        assert!(rule_ctx.bindings.insert(sym, term.clone()).is_none());
    }

    // compute a primitive
    // special logic for ordering-max and ordering-min
    fn do_compute(&mut self, term: Term) -> (Value, Term) {
        let (op, body_terms) = match term.clone() {
            Term::App(op, body) => (
                op,
                body.iter()
                    .map(|v| self.termdag.get_term(*v))
                    .collect::<Vec<_>>(),
            ),
            Term::Lit(lit) => {
                let value = self.egraph.eval_lit(&lit);
                return (value, term);
            }
        };

        match op.as_str() {
            "ordering-max" | "ordering-min" => {
                let body_vals: Vec<Value> = body_terms
                    .iter()
                    .map(|t| match self.termdag.get_id(t) {
                        // Ordering is always called on terms which are in the database,
                        // so it should be the case that the ids are Values
                        TermId::Value(v) => v,
                        _ => panic!("Expected a value in ordering-max"),
                    })
                    .collect();

                assert!(body_vals.len() == 2);
                let (a, b) = if body_vals[0].bits > body_vals[1].bits {
                    (0, 1)
                } else {
                    (1, 0)
                };
                if op.as_str() == "ordering-max" {
                    (body_vals[a], body_terms[a].clone())
                } else {
                    (body_vals[b], body_terms[b].clone())
                }
            }
            _ => {
                let input_types = body_terms
                    .iter()
                    .map(|v| self.typecheck_literal_term(v.clone()))
                    .collect::<Vec<_>>();
                let (primitive, output_type) = self
                    .egraph
                    .term_encoded_typeinfo
                    .lookup_primitive(op, &input_types)
                    .unwrap();
                let body_vals: Vec<Value> = body_terms
                    .iter()
                    .map(|term| {
                        // We may not have a value for children, compute it
                        self.do_compute(term.clone()).0
                    })
                    .collect::<Vec<_>>();
                let output = primitive.apply(&body_vals, self.egraph).unwrap_or_else(|| {
                    panic!("Proof checking failed- primitive did not return a value")
                });

                let output_term = output_type.make_expr(self.egraph, output, &mut self.termdag);

                (output, output_term)
            }
        }
    }

    fn typecheck_literal_term(&self, term: Term) -> ArcSort {
        match term {
            Term::Lit(lit) => self.egraph.term_encoded_typeinfo.infer_literal(&lit),
            Term::App(op, body) => {
                let (_prim, output_type) = self
                    .egraph
                    .term_encoded_typeinfo
                    .lookup_primitive(
                        op,
                        &body
                            .iter()
                            .map(|v| self.typecheck_literal_term(self.termdag.get_term(*v)))
                            .collect::<Vec<_>>(),
                    )
                    .unwrap_or_else(|| panic!("Expected a primitive. Got: {:?}", op));
                output_type
            }
            _ => panic!("Expected a literal term"),
        }
    }

    fn get_term_encoded(&self, name: Symbol) -> &(NormRule, CommandId) {
        self.term_encoded_rules
            .get(&name)
            .unwrap_or_else(|| panic!("get_term_encoded: no rule named '{name}'"))
    }
}