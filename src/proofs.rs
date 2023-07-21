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

    fn make_proof_type(&self, sort: &Symbol) -> String {
        let underscores = "_".repeat(self.desugar.number_underscores);
        let proof_header = include_str!("prooftype.egg");
        let replaced = proof_header.replace('_', &underscores);
        replaced.replace('^', &sort.to_string())
    }

    fn get_proof_type(&self) -> Symbol {
        format!("Proof{}", "_".repeat(self.desugar.number_underscores)).into()
    }

    fn get_proof_term_type(&self) -> Symbol {
        format!("ProofTerm{}", "_".repeat(self.desugar.number_underscores)).into()
    }

    fn proof_func_name(&self) -> Symbol {
        format!("ProofOf{}", "_".repeat(self.desugar.number_underscores)).into()
    }

    fn term_func_name(&self, name: Symbol) -> Symbol {
        format!(
            "{}Term{}",
            name,
            "_".repeat(self.desugar.number_underscores)
        )
        .into()
    }

    // Make a term type for this function
    // which can be put in proofs
    // For tables with merge functions, we need all
    // the inputs.
    // For other terms, just use built-in terms
    fn make_term_table(&self, fdecl: &FunctionDecl) -> Vec<Command> {
        if fdecl.merge.is_none() {
            return vec![];
        }
        let input = fdecl
            .schema
            .input
            .iter()
            .cloned()
            .chain(once(fdecl.schema.output))
            .collect();

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

    fn var_to_term(&self, var: Symbol) -> String {
        let var_type = self.type_info.lookup(self.current_ctx, var).unwrap().name();
        let term_name = self.term_func_name(var_type);
        format!("({term_name} {var})")
    }

    fn get_term(&self, expr: &NormExpr) -> String {
        let expr_type = self.type_info.lookup_expr(self.current_ctx, &expr).unwrap();
        let NormExpr::Call(head, children) = expr;
        if expr_type.has_merge {
            let term_name = self.term_func_name(*head);
            let input_str = ListDisplay(children, " ");
            // put the input and look up the output
            format!("({term_name} {input_str} {expr})")
        } else {
            let term_name = self.term_func_name(expr_type.output.name());
            format!("({term_name} {expr})")
        }
    }

    fn original(&self, expr: &NormExpr) -> String {
        let underscores = "_".repeat(self.desugar.number_underscores);
        let term = self.get_term(expr);

        format!("(Original{underscores} {term})")
    }

    fn add_proofs_action_original(&self, action: &NormAction) -> Vec<Command> {
        match action {
            NormAction::Delete(..) | NormAction::Extract(..) | NormAction::Panic(..) => {
                vec![]
            }
            NormAction::Let(lhs, expr) => self.add_proof_of(expr, self.original(expr)),
            NormAction::Union(lhs, rhs) => {
                panic!("Union should have been desugared by term encoding");
            }
            NormAction::LetLit(lhs, _lit) => vec![],
            NormAction::LetVar(..) => vec![],
            NormAction::Set(expr, var) => self.add_proof_of(expr, self.original(expr)),
        }
    }

    fn add_proof_of(&self, expr: &NormExpr, proof: String) -> Vec<Command> {
        let term = self.get_term(expr);
        let expr_type = self.type_info.lookup_expr(self.current_ctx, &expr).unwrap();
        let proof_func = self.proof_func_name();
        self.parse_program(&format!("(set ({proof_func} {term}) {proof})"))
            .unwrap()
    }

    fn add_proofs_command(&self, command: NCommand) -> Vec<Command> {
        match &command {
            NCommand::Function(fdecl) => {
                vec_append(vec![command.to_command()], self.make_term_table(fdecl))
            }
            NCommand::Sort(sort, _pre) => vec_append(
                vec![command.to_command()],
                self.parse_program(&self.make_proof_type(sort)).unwrap(),
            ),
            NCommand::NormAction(action) => vec_append(
                vec![command.to_command()],
                self.add_proofs_action_original(action),
            ),
            _ => vec![command.to_command()],
        }
    }

    pub(crate) fn add_proofs(&mut self, program: Vec<NormCommand>) -> Vec<Command> {
        let mut res = vec![];

        if !self.proof_header_added {
            res.extend(self.proof_header());
            self.proof_header_added = true;
        }

        for command in program {
            self.current_ctx = command.metadata.id;
            res.extend(self.add_proofs_command(command.command));
        }
        res
    }
}
