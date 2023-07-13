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
        let replaced = proofheader.replace("_", &underscores);
        self.parse_program(&replaced).unwrap()
    }

    fn make_proof_type(&self, sort: &Symbol) -> String {
        let underscores = "_".repeat(self.desugar.number_underscores);
        let proof_header = include_str!("prooftype.egg");
        let replaced = proof_header.replace("_", &underscores);
        replaced.replace("^", &sort.to_string())
    }

    fn get_proof_type(&self, sort: &Symbol) -> Symbol {
        format!(
            "{}Proof{}",
            sort,
            "_".repeat(self.desugar.number_underscores)
        )
        .into()
    }

    fn proof_func_name(&self, name: &Symbol) -> Symbol {
        format!(
            "{}_Proof{}",
            name,
            "_".repeat(self.desugar.number_underscores)
        )
        .into()
    }

    fn make_proof_table(&self, fdecl: &FunctionDecl) -> Command {
        Command::Function(FunctionDecl {
            name: self.proof_func_name(&fdecl.name),
            schema: Schema {
                input: fdecl.schema.input.clone(),
                output: self.get_proof_type(&fdecl.schema.output),
            },
            default: None,
            merge: Some(Expr::Var("new".into())),
            merge_action: vec![],
            cost: None,
            unextractable: false,
        })
    }

    fn add_proofs_command(&self, command: NCommand) -> Vec<Command> {
        match command {
            NCommand::Function(fdecl) => {
                vec![command.to_command(), self.make_proof_table(&fdecl)]
            }
            NCommand::Sort(sort, _pre) => vec_append(
                vec![command.to_command()],
                self.parse_program(&self.make_proof_type(&sort)).unwrap(),
            ),
            _ => vec![command.to_command()],
        }
    }

    fn add_proofs(&mut self, program: Vec<NormCommand>) -> Vec<Command> {
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
