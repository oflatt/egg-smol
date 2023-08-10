use crate::*;

use crate::ast::desugar::Desugar;

pub const RULE_PROOF_KEYWORD: &str = "rule-proof";

#[derive(Default, Clone)]
pub(crate) struct ProofState {
    pub(crate) current_ctx: CommandId,
    pub(crate) desugar: Desugar,
    pub(crate) type_info: TypeInfo,
    pub(crate) term_header_added: bool,
    pub(crate) proof_header_added: bool,
}

impl ProofState {
    fn proof_header(&self) -> Vec<Command> {
        let underscores = "_".repeat(self.desugar.number_underscores);
        let proofheader = include_str!("proofheader.egg");
        let replaced = proofheader.replace('_', &underscores);
        self.parse_program(&replaced).unwrap()
    }

    fn get_proof_term_type(&self) -> Symbol {
        format!("ProofTerm{}", "_".repeat(self.desugar.number_underscores)).into()
    }

    pub(crate) fn proof_func_name(&self) -> Symbol {
        format!("ProofOf{}", "_".repeat(self.desugar.number_underscores)).into()
    }

    pub fn term_func_ending(&self) -> String {
        format!("T{}", "_".repeat(self.desugar.number_underscores))
    }

    fn term_func_name(&self, name: Symbol) -> Symbol {
        format!("{}{}", name, self.term_func_ending()).into()
    }

    // Make a term type for this function
    // which can be put in proofs
    fn make_term_table(&self, fdecl: &NormFunctionDecl) -> Vec<Command> {
        let types = self.type_info.func_types.get(&fdecl.name).unwrap();
        let input = if types.is_datatype {
            // datatypes are already terms, just wrap
            vec![fdecl.schema.output.clone()]
        } else {
            fdecl
                .schema
                .input
                .iter()
                .cloned()
                .chain(once(fdecl.schema.output))
                .collect()
        };

        vec![Command::Function(FunctionDecl {
            name: self.term_func_name(fdecl.name),
            schema: Schema {
                input,
                output: self.get_proof_term_type(),
            },
            default: None,
            merge: None,
            merge_action: vec![],
            cost: None,
            unextractable: false,
        })]
    }

    fn make_prim_term_tables(&self) -> Vec<Command> {
        let mut res = vec![];
        for (name, _sort) in TypeInfo::default().prim_sorts {
            res.push(Command::Function(FunctionDecl {
                name: self.term_func_name(name),
                schema: Schema {
                    input: vec![name],
                    output: self.get_proof_term_type(),
                },
                default: None,
                merge: None,
                merge_action: vec![],
                cost: None,
                unextractable: false,
            }))
        }
        res
    }

    fn get_proof(&self, expr: &NormExpr, output: Option<Symbol>) -> String {
        let term = self.get_term(expr, output);
        let proof_func = self.proof_func_name();
        format!("({proof_func} {term})")
    }

    fn var_to_proof(&self, var: Symbol) -> String {
        let term = self.var_to_term(var);
        let proof_func = self.proof_func_name();
        format!(
            "({proof_func} {term})",
            proof_func = proof_func,
            term = term
        )
    }

    fn var_to_term(&self, var: Symbol) -> String {
        let var_type = self.type_info.lookup(self.current_ctx, var).unwrap();
        let term_name = self.term_func_name(var_type.name());
        format!("({term_name} {var})", term_name = term_name, var = var)
    }

    fn get_term(&self, expr: &NormExpr, result: Option<Symbol>) -> String {
        let expr_type = self.type_info.lookup_expr(self.current_ctx, expr).unwrap();
        let NormExpr::Call(head, children) = expr;
        if !expr_type.is_datatype {
            let output = if let Some(var) = result {
                var.to_string()
            } else {
                expr.to_string()
            };
            let term_name = self.term_func_name(*head);
            let input_str = ListDisplay(children, " ");
            // put the input and look up the output
            format!("({term_name} {input_str} {output})")
        } else {
            assert!(
                result.is_none(),
                "Non-merge terms should not have results. Got: {}",
                expr
            );
            let term_name = self.term_func_name(*head);
            format!("({term_name} {expr})")
        }
    }

    pub(crate) fn original_name(&self) -> String {
        format!("Original{}", "_".repeat(self.desugar.number_underscores))
    }

    pub(crate) fn rule_proof_constructor(&self) -> String {
        format!("RuleProof{}", "_".repeat(self.desugar.number_underscores))
    }

    fn add_proofs_action_original(&self, action: &NormAction) -> Vec<Command> {
        let original_prf_fn = |term| format!("({} {})", self.original_name(), term);
        match action {
            NormAction::Delete(..)
            | NormAction::Extract(..)
            | NormAction::Panic(..)
            | NormAction::Print(..) => {
                vec![]
            }
            NormAction::Let(_lhs, expr) => self
                .add_proof_of(expr, original_prf_fn, None)
                .into_iter()
                .map(Command::Action)
                .collect(),
            NormAction::Union(_lhs, _rhs) => {
                panic!("Union should have been desugared by term encoding");
            }
            NormAction::LetLit(_lhs, _lit) => vec![],
            NormAction::LetVar(..) => vec![],
            NormAction::Set(expr, var) => self
                .add_proof_of(expr, original_prf_fn, Some(*var))
                .into_iter()
                .map(Command::Action)
                .collect(),
        }
    }

    fn add_proof_of<ProofFunc>(
        &self,
        expr: &NormExpr,
        proof: ProofFunc,
        result: Option<Symbol>,
    ) -> Vec<Action>
    where
        ProofFunc: Fn(String) -> String,
    {
        let expr_type = self.type_info.lookup_expr(self.current_ctx, expr).unwrap();
        // no proof needed for primitives
        // or just lookups
        if expr_type.is_primitive
            || (!expr_type.is_datatype && !expr_type.has_default && result.is_none())
        {
            return vec![];
        }
        let term = self.get_term(expr, result);
        let proof_func = self.proof_func_name();
        let proof = proof(term.clone());
        let res = self.parse_actions(vec![format!("(set ({proof_func} {term}) {proof})")]);
        assert!(res.len() == 1);
        vec![res.into_iter().next().unwrap()]
    }

    fn fact_proof(&self, fact: &NormFact) -> Option<String> {
        match fact {
            NormFact::Assign(_lhs, expr) => Some(self.get_proof(expr, None)),
            _ => None,
        }
    }

    pub(crate) fn proof_null_constructor(&self) -> String {
        format!("ProofNull{}", "_".repeat(self.desugar.number_underscores))
    }

    fn proof_null(&self) -> String {
        format!("({})", self.proof_null_constructor())
    }

    pub(crate) fn proof_cons_constructor(&self) -> String {
        format!("ProofCons{}", "_".repeat(self.desugar.number_underscores))
    }

    fn proof_cons(&self, head: String, tail: String) -> String {
        let cons = self.proof_cons_constructor();
        format!("({cons} {head} {tail})")
    }

    fn rule_proof(&self, rule: &NormRule) -> String {
        let mut res = self.proof_null();
        for fact in rule.body.iter().rev() {
            if let Some(prf) = self.fact_proof(fact) {
                res = self.proof_cons(prf, res);
            }
        }
        res
    }

    fn actions_add_proof<ProofFunc>(
        &mut self,
        actions: &Vec<NormAction>,
        // The proof func wraps a proof around the
        // term being proven
        prf: &ProofFunc,
    ) -> Vec<Action>
    where
        ProofFunc: Fn(String) -> String,
    {
        let mut res = vec![];
        for action in actions {
            match action {
                NormAction::Let(_lhs, expr) => {
                    res.extend(self.add_proof_of(expr, prf, None));
                }
                NormAction::Set(expr, var) => {
                    res.extend(self.add_proof_of(expr, prf, Some(*var)));
                }
                NormAction::Union(..) => panic!("Union should have been desugared"),
                _ => {}
            }
            res.push(action.to_action());
        }
        res
    }

    fn rule_add_proofs(&mut self, rule: &NormRule, name: Symbol) -> Vec<Action> {
        let rule_proof = self.fresh().as_str();
        let rule_name = self.fresh().as_str();
        let rule_proof_name = self.rule_proof_constructor();
        let mut res = self.parse_actions(vec![
            format!("(let {rule_proof} {})", self.rule_proof(rule)),
            format!("(let {rule_name} \"{name}\")"),
        ]);
        let proof_func =
            |term: String| format!("({rule_proof_name} {rule_name} {rule_proof} {})", term);
        res.extend(self.actions_add_proof(&rule.head, &proof_func));

        res
    }

    fn fresh(&mut self) -> Symbol {
        self.desugar.fresh()
    }

    // TODO this terrible function can go away if we desugar merge functions
    pub(crate) fn instrument_merge_actions(&mut self, fdecl: &NormFunctionDecl) -> Vec<Action> {
        if fdecl.merge.is_none() {
            assert!(fdecl.merge_action.is_empty());
            return vec![];
        }
        let children = fdecl
            .schema
            .input
            .iter()
            .enumerate()
            .map(|(i, _)| self.type_info.merge_fn_child_name(i))
            .collect::<Vec<_>>();
        let name = fdecl.name;
        let term_name = self.term_func_name(name);
        let proof_func = self.proof_func_name();
        let old_prf = format!(
            "({proof_func} ({term_name} {} old))",
            ListDisplay(&children, " ")
        );
        let new_expr = format!(
            "({proof_func} ({term_name} {} new))",
            ListDisplay(&children, " ")
        );
        let merged_term = format!(
            "({term_name} {} {})",
            ListDisplay(&children, " "),
            fdecl.merge.as_ref().unwrap()
        );
        let rule_prf_constructor = self.rule_proof_constructor();

        let rule_name = format!("\"{name}-merge-fn__\"");
        let rule_name_var = self.fresh().as_str();
        let rule_prf = self.proof_cons(old_prf, self.proof_cons(new_expr, self.proof_null()));
        let rule_prf_name = self.fresh().as_str();
        let prf_fn =
            |term: String| format!("({rule_prf_constructor} {rule_name} {rule_prf} {})", term);

        vec_append(
            self.parse_actions(vec![
                format!("(let {rule_name_var} {rule_name})"),
                format!("(let {rule_prf_name} {rule_prf})"),
                format!(
                    "(set ({proof_func} {merged_term}) {})",
                    prf_fn(merged_term.clone())
                ),
            ]),
            self.actions_add_proof(&fdecl.merge_action, &prf_fn),
        )
    }

    pub(crate) fn instrument_fdecl(&mut self, fdecl: &NormFunctionDecl) -> FunctionDecl {
        FunctionDecl {
            name: fdecl.name,
            schema: fdecl.schema.clone(),
            merge: fdecl.merge.clone(),
            merge_action: self.instrument_merge_actions(fdecl),
            cost: fdecl.cost,
            unextractable: fdecl.unextractable,
            default: fdecl.default.clone(),
        }
    }

    fn add_proofs_command(&mut self, command: NCommand) -> Vec<Command> {
        match &command {
            NCommand::Function(fdecl) => vec_append(
                self.make_term_table(fdecl),
                vec![Command::Function(self.instrument_fdecl(fdecl))],
            ),
            NCommand::Sort(_sort, _pre) => vec![command.to_command()],
            NCommand::NormAction(action) => vec_append(
                self.add_proofs_action_original(action),
                vec![command.to_command()],
            ),
            NCommand::NormRule {
                name,
                rule,
                ruleset,
            } => {
                vec![Command::Rule {
                    name: *name,
                    ruleset: *ruleset,
                    rule: Rule {
                        body: rule.body.iter().map(|e| e.to_fact()).collect(),
                        head: self.rule_add_proofs(rule, *name),
                    },
                }]
            }
            NCommand::GetProof(..) => panic!("GetProof should have been desugared"),
            NCommand::LookupProof(expr) => self
                .parse_actions(vec![format!("(print {})", self.get_proof(expr, None))])
                .into_iter()
                .map(Command::Action)
                .collect(),
            _ => vec![command.to_command()],
        }
    }

    pub(crate) fn add_proofs(&mut self, program: Vec<NormCommand>) -> Vec<Command> {
        let mut res = vec![];

        if !self.proof_header_added {
            res.extend(self.proof_header());
            res.extend(self.make_prim_term_tables());
            self.proof_header_added = true;
        }

        for command in program {
            self.current_ctx = command.metadata.id;
            res.extend(self.add_proofs_command(command.command));
        }
        res
    }
}
