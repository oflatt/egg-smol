use crate::*;

fn desugar_datatype(name: Symbol, variants: Vec<Variant>) -> Vec<NCommand> {
    vec![NCommand::Sort(name, None)]
        .into_iter()
        .chain(variants.into_iter().map(|variant| {
            NCommand::Function(NormFunctionDecl {
                name: variant.name,
                schema: Schema {
                    input: variant.types,
                    output: name,
                },
                merge: None,
                merge_action: vec![],
                default: None,
                cost: variant.cost,
                unextractable: false,
            })
        }))
        .collect()
}

fn desugar_rewrite(
    ruleset: Symbol,
    name: Symbol,
    rewrite: &Rewrite,
    desugar: &mut Desugar,
) -> Vec<NCommand> {
    let var = Symbol::from("rewrite_var__");
    let rule = Rule {
        body: [Fact::Eq(vec![Expr::Var(var), rewrite.lhs.clone()])]
            .into_iter()
            .chain(rewrite.conditions.clone())
            .collect(),
        head: vec![Action::Union(Expr::Var(var), rewrite.rhs.clone())],
    };
    vec![NCommand::NormRule {
        ruleset,
        name,
        rule: flatten_rule(rule, desugar),
    }]
}

fn desugar_birewrite(
    ruleset: Symbol,
    name: Symbol,
    rewrite: &Rewrite,
    desugar: &mut Desugar,
) -> Vec<NCommand> {
    let rw2 = Rewrite {
        lhs: rewrite.rhs.clone(),
        rhs: rewrite.lhs.clone(),
        conditions: rewrite.conditions.clone(),
    };
    desugar_rewrite(ruleset, format!("{}=>", name).into(), rewrite, desugar)
        .into_iter()
        .chain(desugar_rewrite(
            ruleset,
            format!("{}<=", name).into(),
            &rw2,
            desugar,
        ))
        .collect()
}

fn normalize_expr(
    lhs_in: Symbol,
    expr: &Expr,
    desugar: &mut Desugar,
    res: &mut Vec<NormFact>,
    constraints: &mut Vec<(Symbol, Symbol)>,
    bound: &mut HashSet<Symbol>,
    cache: &mut HashMap<Expr, Symbol>,
) {
    if let Some(var) = cache.get(expr) {
        if bound.insert(lhs_in) {
            res.push(NormFact::AssignVar(lhs_in, *var));
        } else {
            constraints.push((lhs_in, *var));
        }
        return;
    }
    let lhs = if bound.insert(lhs_in) {
        lhs_in
    } else {
        let fresh = desugar.fresh();
        constraints.push((fresh, lhs_in));
        fresh
    };

    if let Expr::Var(v) = expr {
        res.push(NormFact::AssignVar(lhs, *v));
        return;
    }

    match expr {
        Expr::Lit(l) => res.push(NormFact::AssignLit(lhs, l.clone())),
        Expr::Var(_v) => panic!("Should have been handled above"),

        Expr::Call(f, children) if TypeInfo::default().is_primitive_func(*f) => {
            let mut new_children = vec![];
            for child in children {
                match child {
                    Expr::Var(v) => {
                        new_children.push(*v);
                    }
                    Expr::Lit(l) => {
                        let fresh = desugar.fresh();
                        res.push(NormFact::AssignLit(fresh, l.clone()));
                        new_children.push(fresh);
                    }
                    _ => {
                        let fresh = desugar.fresh();
                        normalize_expr(fresh, child, desugar, res, constraints, bound, cache);
                        new_children.push(fresh);
                    }
                }
            }

            res.push(NormFact::Compute(lhs, NormExpr::Call(*f, new_children)))
        }
        Expr::Call(f, children) => {
            let mut new_children = vec![];
            for child in children {
                match child {
                    Expr::Var(v) => {
                        if desugar.global_variables.contains(v) {
                            let fresh = desugar.fresh();
                            new_children.push(fresh);
                            constraints.push((fresh, *v));
                        } else if bound.insert(*v) {
                            new_children.push(*v);
                        } else {
                            let new = desugar.fresh();
                            new_children.push(new);
                            constraints.push((new, *v));
                        }
                    }
                    _ => {
                        let fresh = desugar.fresh();
                        bound.insert(fresh);
                        normalize_expr(fresh, child, desugar, res, constraints, bound, cache);
                        new_children.push(fresh);
                    }
                }
            }
            res.push(NormFact::Assign(lhs, NormExpr::Call(*f, new_children)))
        }
    };
    cache.insert(expr.clone(), lhs);
}

fn flatten_equalities(equalities: Vec<(Symbol, Expr)>, desugar: &mut Desugar) -> Vec<NormFact> {
    let mut res = vec![];
    let mut bound_variables: HashSet<Symbol> = Default::default();
    let mut constraints: Vec<(Symbol, Symbol)> = Default::default();
    let mut cache = Default::default();
    let bound = |var, desugar: &Desugar, bound_variables: &HashSet<Symbol>| {
        desugar.global_variables.contains(&var) || bound_variables.contains(&var)
    };

    for (lhs, rhs) in equalities {
        if let Expr::Var(rhs_v) = rhs {
            if bound(rhs_v, desugar, &bound_variables) && bound(lhs, desugar, &bound_variables) {
                constraints.push((lhs, rhs_v));
            } else if bound(lhs, desugar, &bound_variables) {
                res.push(NormFact::AssignVar(rhs_v, lhs));
                bound_variables.insert(rhs_v);
            } else if bound(rhs_v, desugar, &bound_variables) {
                res.push(NormFact::AssignVar(lhs, rhs_v));
                bound_variables.insert(lhs);
            } else {
                constraints.push((lhs, rhs_v));
            }
        }
        // lhs is already bound
        else if bound(lhs, desugar, &bound_variables) {
            let fresh = desugar.fresh();
            normalize_expr(
                fresh,
                &rhs,
                desugar,
                &mut res,
                &mut constraints,
                &mut bound_variables,
                &mut cache,
            );
            constraints.push((fresh, lhs));
        } else {
            normalize_expr(
                lhs,
                &rhs,
                desugar,
                &mut res,
                &mut constraints,
                &mut bound_variables,
                &mut cache,
            );
        }
    }

    for (lhs, rhs) in constraints {
        res.push(NormFact::ConstrainEq(lhs, rhs));
    }

    res
}

fn flatten_facts(facts: &Vec<Fact>, desugar: &mut Desugar) -> Vec<NormFact> {
    let mut equalities = vec![];
    for fact in facts {
        match fact {
            Fact::Eq(args) => {
                assert!(args.len() == 2);
                let lhs = &args[0];
                let rhs = &args[1];
                if let Expr::Var(v) = lhs {
                    equalities.push((*v, rhs.clone()));
                } else if let Expr::Var(v) = rhs {
                    equalities.push((*v, lhs.clone()));
                } else {
                    let fresh = desugar.fresh();
                    equalities.push((fresh, lhs.clone()));
                    equalities.push((fresh, rhs.clone()));
                }
            }
            Fact::Fact(expr) => {
                // we can drop facts that are
                // just a variable
                if let Expr::Var(_v) = expr {
                } else {
                    equalities.push((desugar.fresh(), expr.clone()));
                }
            }
        }
    }

    flatten_equalities(equalities, desugar)
}

fn flatten_actions(actions: &Vec<Action>, desugar: &mut Desugar) -> Vec<NormAction> {
    let mut add_expr = |expr: Expr, res: &mut Vec<NormAction>| -> Symbol {
        // TODO using new memo every time because re-ordering table accesses is bad
        desugar.expr_to_flat_actions(&expr, res, &mut Default::default())
    };

    let mut res = vec![];

    for action in actions {
        match action {
            Action::Let(symbol, expr) => {
                let added = add_expr(expr.clone(), &mut res);
                assert_ne!(*symbol, added);
                res.push(NormAction::LetVar(*symbol, added));
            }
            Action::Set(symbol, exprs, rhs) => {
                let set = NormAction::Set(
                    NormExpr::Call(
                        *symbol,
                        exprs
                            .clone()
                            .into_iter()
                            .map(|ex| add_expr(ex, &mut res))
                            .collect(),
                    ),
                    add_expr(rhs.clone(), &mut res),
                );
                res.push(set);
            }
            Action::Extract(expr, variants) => {
                let added = add_expr(expr.clone(), &mut res);
                let added_variants = add_expr(variants.clone(), &mut res);
                res.push(NormAction::Extract(added, added_variants));
            }
            Action::Print(expr) => {
                let added = add_expr(expr.clone(), &mut res);
                res.push(NormAction::Print(added));
            }
            Action::Delete(symbol, exprs) => {
                let del = NormAction::Delete(NormExpr::Call(
                    *symbol,
                    exprs
                        .clone()
                        .into_iter()
                        .map(|ex| add_expr(ex, &mut res))
                        .collect(),
                ));
                res.push(del);
            }
            Action::Union(lhs, rhs) => {
                let un = NormAction::Union(
                    add_expr(lhs.clone(), &mut res),
                    add_expr(rhs.clone(), &mut res),
                );
                res.push(un);
            }
            Action::Panic(msg) => {
                res.push(NormAction::Panic(msg.clone()));
            }
            Action::Expr(expr) => {
                add_expr(expr.clone(), &mut res);
            }
        };
    }

    res
}

fn give_unique_names(desugar: &mut Desugar, facts: Vec<NormFact>) -> Vec<NormFact> {
    let mut name_used: HashSet<Symbol> = Default::default();
    let mut constraints: Vec<NormFact> = Default::default();
    let mut res = vec![];
    for fact in facts {
        let mut name_used_immediately: HashSet<Symbol> = Default::default();
        let mut constraints_before = vec![];
        let new_fact = fact.map_def_use(&mut |var, is_def| {
            if is_def {
                if name_used.insert(var) {
                    name_used_immediately.insert(var);
                    var
                } else {
                    let fresh = desugar.fresh();
                    // typechecking BS- for primitives
                    // we need to define variables before they are used
                    if name_used_immediately.contains(&var) {
                        constraints.push(NormFact::ConstrainEq(fresh, var));
                    } else {
                        constraints_before.push(NormFact::ConstrainEq(fresh, var));
                    }
                    fresh
                }
            } else {
                var
            }
        });
        res.extend(constraints_before);
        res.push(new_fact);
    }

    res.extend(constraints);
    res
}

fn flatten_rule(rule: Rule, desugar: &mut Desugar) -> NormRule {
    let flat_facts = flatten_facts(&rule.body, desugar);
    let with_unique_names = give_unique_names(desugar, flat_facts);

    NormRule {
        head: flatten_actions(&rule.head, desugar),
        body: with_unique_names,
    }
}

fn desugar_schedule(desugar: &mut Desugar, schedule: &Schedule) -> NormSchedule {
    match schedule {
        Schedule::Repeat(num, schedule) => {
            let norm_schedule = desugar_schedule(desugar, schedule);
            NormSchedule::Repeat(*num, Box::new(norm_schedule))
        }
        Schedule::Saturate(schedule) => {
            let norm_schedule = desugar_schedule(desugar, schedule);
            NormSchedule::Saturate(Box::new(norm_schedule))
        }
        Schedule::Run(run_config) => {
            let norm_run_config = desugar_run_config(desugar, run_config);
            NormSchedule::Run(norm_run_config)
        }
        Schedule::Sequence(schedules) => {
            let norm_schedules = schedules
                .iter()
                .map(|schedule| desugar_schedule(desugar, schedule))
                .collect();
            NormSchedule::Sequence(norm_schedules)
        }
    }
}

fn desugar_run_config(desugar: &mut Desugar, run_config: &RunConfig) -> NormRunConfig {
    let RunConfig { ruleset, until } = run_config;
    NormRunConfig {
        ruleset: *ruleset,
        until: until.clone().map(|facts| flatten_facts(&facts, desugar)),
    }
}

fn add_semi_naive_rule(desugar: &mut Desugar, rule: Rule) -> Option<Rule> {
    let mut new_rule = rule;
    // only add new rule when there is Call in body to avoid adding same rule.
    let mut add_new_rule = false;

    for head_slice in new_rule.head.iter_mut() {
        match head_slice {
            Action::Set(_, _, value) => {
                // if the right hand side is a function call,
                // move it to body so seminaive fires
                if let Expr::Call(_, _) = value {
                    add_new_rule = true;
                    let mut eq_vec: Vec<Expr> = Vec::new();
                    let fresh_symbol = desugar.fresh();
                    eq_vec.push(Expr::Var(fresh_symbol));
                    eq_vec.push(value.clone());
                    new_rule.body.push(Fact::Eq(eq_vec));
                    *value = Expr::Var(fresh_symbol);
                };
            }

            // move let binding to body.
            Action::Let(symbol, expr) => {
                let eq_vec: Vec<Expr> = vec![Expr::Var(*symbol), expr.clone()];
                new_rule.body.push(Fact::Eq(eq_vec));
            }
            _ => (),
        }
    }

    if add_new_rule {
        // remove all let action
        new_rule
            .head
            .retain_mut(|action| !matches!(action, Action::Let(_, _)));
        log::debug!("Added a semi-naive desugared rule:\n{}", new_rule);
        Some(new_rule)
    } else {
        None
    }
}

pub struct Desugar {
    next_fresh: usize,
    next_command_id: usize,
    pub(crate) parser: ast::parse::ProgramParser,
    pub(crate) action_parser: ast::parse::ActionParser,
    pub(crate) fact_parser: ast::parse::FactParser,
    // TODO fix getting fresh names using modules
    pub(crate) number_underscores: usize,
    pub(crate) global_variables: HashSet<Symbol>,
}

impl Default for Desugar {
    fn default() -> Self {
        Self {
            next_fresh: Default::default(),
            next_command_id: Default::default(),
            // these come from lalrpop and don't have default impls
            parser: ast::parse::ProgramParser::new(),
            action_parser: ast::parse::ActionParser::new(),
            fact_parser: ast::parse::FactParser::new(),
            number_underscores: 3,
            global_variables: Default::default(),
        }
    }
}

pub(crate) fn desugar_simplify(
    desugar: &mut Desugar,
    expr: &Expr,
    schedule: &Schedule,
) -> Vec<NCommand> {
    let mut res = vec![NCommand::Push(1)];
    let lhs = desugar.fresh();
    res.extend(
        flatten_actions(&vec![Action::Let(lhs, expr.clone())], desugar)
            .into_iter()
            .map(NCommand::NormAction),
    );
    res.push(NCommand::RunSchedule(desugar_schedule(desugar, schedule)));
    res.extend(
        desugar_command(
            Command::Extract {
                variants: 0,
                fact: Fact::Fact(Expr::Var(lhs)),
            },
            desugar,
            false,
            false,
        )
        .unwrap()
        .into_iter()
        .map(|c| c.command),
    );

    res.push(NCommand::Pop(1));
    res
}

pub(crate) fn desugar_calc(
    desugar: &mut Desugar,
    idents: Vec<IdentSort>,
    exprs: Vec<Expr>,
    seminaive_transform: bool,
) -> Result<Vec<NCommand>, Error> {
    let mut res = vec![];

    // first, push all the idents
    for IdentSort { ident, sort } in idents {
        res.push(Command::Declare { name: ident, sort });
    }

    // now, for every pair of exprs we need to prove them equal
    for expr1and2 in exprs.windows(2) {
        let expr1 = &expr1and2[0];
        let expr2 = &expr1and2[1];
        res.push(Command::Push(1));

        // add the two exprs
        res.push(Command::Action(Action::Expr(expr1.clone())));
        res.push(Command::Action(Action::Expr(expr2.clone())));

        res.push(Command::RunSchedule(Schedule::Saturate(Box::new(
            Schedule::Run(RunConfig {
                ruleset: "".into(),
                until: Some(vec![Fact::Eq(vec![expr1.clone(), expr2.clone()])]),
            }),
        ))));

        res.push(Command::Check(vec![Fact::Eq(vec![
            expr1.clone(),
            expr2.clone(),
        ])]));

        res.push(Command::Pop(1));
    }

    desugar_commands(res, desugar, false, seminaive_transform)
        .map(|cmds| cmds.into_iter().map(|cmd| cmd.command).collect())
}

pub(crate) fn rewrite_name(rewrite: &Rewrite) -> String {
    rewrite.to_string().replace('\"', "'")
}

pub(crate) fn desugar_command(
    command: Command,
    desugar: &mut Desugar,
    get_all_proofs: bool,
    seminaive_transform: bool,
) -> Result<Vec<NormCommand>, Error> {
    let res = match command {
        Command::SetOption { name, value } => {
            vec![NCommand::SetOption { name, value }]
        }
        Command::Function(fdecl) => desugar.desugar_function(&fdecl),
        Command::Declare { name, sort } => desugar.declare(name, sort),
        Command::Datatype { name, variants } => desugar_datatype(name, variants),
        Command::Rewrite(ruleset, rewrite) => {
            desugar_rewrite(ruleset, rewrite_name(&rewrite).into(), &rewrite, desugar)
        }
        Command::BiRewrite(ruleset, rewrite) => {
            desugar_birewrite(ruleset, rewrite_name(&rewrite).into(), &rewrite, desugar)
        }
        Command::Include(file) => {
            let s = std::fs::read_to_string(&file)
                .unwrap_or_else(|_| panic!("Failed to read file {file}"));
            return desugar_commands(
                desugar.parse_program(&s)?,
                desugar,
                get_all_proofs,
                seminaive_transform,
            );
        }
        Command::Rule {
            ruleset,
            mut name,
            rule,
        } => {
            if name == "".into() {
                name = rule.to_string().replace('\"', "'").into();
            }

            let mut result = vec![NCommand::NormRule {
                ruleset,
                name,
                rule: flatten_rule(rule.clone(), desugar),
            }];

            if seminaive_transform {
                let seminaive_name = format!("{}___seminaive", name);
                if let Some(new_rule) = add_semi_naive_rule(desugar, rule) {
                    result.push(NCommand::NormRule {
                        ruleset,
                        name: seminaive_name.into(),
                        rule: flatten_rule(new_rule, desugar),
                    });
                }
            }

            result
        }
        Command::Sort(sort, option) => vec![NCommand::Sort(sort, option)],
        // TODO ignoring cost for now
        Command::AddRuleset(name) => vec![NCommand::AddRuleset(name)],
        Command::Action(action) => flatten_actions(&vec![action], desugar)
            .into_iter()
            .map(NCommand::NormAction)
            .collect(),
        Command::Simplify { expr, schedule } => desugar_simplify(desugar, &expr, &schedule),
        Command::Calc(idents, exprs) => desugar_calc(desugar, idents, exprs, seminaive_transform)?,
        Command::RunSchedule(sched) => {
            let mut res = vec![NCommand::RunSchedule(desugar_schedule(desugar, &sched))];
            if get_all_proofs {
                res.push(NCommand::CheckProof);
            }
            res
        }
        // TODO add variants to extract action
        Command::Extract {
            variants: _variants,
            fact,
        } => {
            let fresh = desugar.fresh();
            let fresh_ruleset = desugar.fresh();
            let desugaring = if let Fact::Fact(Expr::Var(v)) = fact {
                format!("(extract {v})")
            } else {
                format!(
                    "(check {fact})
                    (ruleset {fresh_ruleset})
                    (rule ((= {fresh} {fact}))
                          ((extract {fresh}))
                          :ruleset {fresh_ruleset})
                    (run {fresh_ruleset} 1)"
                )
            };

            desugar
                .desugar_program(
                    desugar.parse_program(&desugaring).unwrap(),
                    get_all_proofs,
                    seminaive_transform,
                )?
                .into_iter()
                .map(|cmd| cmd.command)
                .collect()
        }
        Command::Check(facts) => {
            vec![NCommand::Check(flatten_facts(&facts, desugar))]
        }
        Command::CheckProof => vec![NCommand::CheckProof],
        Command::GetProof(query) => desugar.desugar_get_proof(&query)?,
        Command::LookupProof(expr) => match &expr {
            Expr::Call(f, args) => {
                if !args.is_empty() {
                    return Err(Error::LookupProofRequiresExpr(expr.to_string()));
                }
                vec![NCommand::LookupProof(NormExpr::Call(*f, vec![]))]
            }
            _ => {
                return Err(Error::LookupProofRequiresExpr(expr.to_string()));
            }
        },
        Command::PrintTable(symbol, size) => vec![NCommand::PrintTable(symbol, size)],
        Command::PrintSize(symbol) => vec![NCommand::PrintSize(symbol)],
        Command::Output { file, exprs } => vec![NCommand::Output { file, exprs }],
        Command::Push(num) => {
            vec![NCommand::Push(num)]
        }
        Command::Pop(num) => {
            vec![NCommand::Pop(num)]
        }
        Command::Fail(cmd) => {
            let mut desugared = desugar_command(*cmd, desugar, false, seminaive_transform)?;

            let last = desugared.pop().unwrap();
            desugared.push(NormCommand {
                metadata: last.metadata,
                command: NCommand::Fail(Box::new(last.command)),
            });
            return Ok(desugared);
        }
        Command::Input { name, file } => {
            vec![NCommand::Input { name, file }]
        }
    };

    for cmd in &res {
        if let NCommand::NormAction(action) = cmd {
            action.map_def_use(&mut |var, is_def| {
                if is_def {
                    desugar.global_variables.insert(var);
                }
                var
            });
        }
    }

    Ok(res
        .into_iter()
        .map(|c| NormCommand {
            metadata: Metadata {
                id: desugar.get_new_id(),
            },
            command: c,
        })
        .collect())
}

pub(crate) fn desugar_commands(
    program: Vec<Command>,
    desugar: &mut Desugar,
    get_all_proofs: bool,
    seminaive_transform: bool,
) -> Result<Vec<NormCommand>, Error> {
    let mut res = vec![];
    for command in program {
        let desugared = desugar_command(command, desugar, get_all_proofs, seminaive_transform)?;
        res.extend(desugared);
    }
    Ok(res)
}

impl Clone for Desugar {
    fn clone(&self) -> Self {
        Self {
            next_fresh: self.next_fresh,
            next_command_id: self.next_command_id,
            parser: ast::parse::ProgramParser::new(),
            action_parser: ast::parse::ActionParser::new(),
            fact_parser: ast::parse::FactParser::new(),
            number_underscores: self.number_underscores,
            global_variables: self.global_variables.clone(),
        }
    }
}

impl Desugar {
    pub fn merge_ruleset_name(&self) -> Symbol {
        Symbol::from(format!(
            "merge_ruleset{}",
            "_".repeat(self.number_underscores)
        ))
    }

    pub fn fresh(&mut self) -> Symbol {
        self.next_fresh += 1;
        format!(
            "v{}{}",
            self.next_fresh - 1,
            "_".repeat(self.number_underscores)
        )
        .into()
    }

    pub fn get_new_id(&mut self) -> CommandId {
        let res = self.next_command_id;
        self.next_command_id += 1;
        res
    }

    pub(crate) fn desugar_program(
        &mut self,
        program: Vec<Command>,
        get_all_proofs: bool,
        seminaive_transform: bool,
    ) -> Result<Vec<NormCommand>, Error> {
        let res = desugar_commands(program, self, get_all_proofs, seminaive_transform)?;
        Ok(res)
    }

    fn expr_to_flat_actions(
        &mut self,
        expr: &Expr,
        res: &mut Vec<NormAction>,
        memo: &mut HashMap<Expr, Symbol>,
    ) -> Symbol {
        if let Some(existing) = memo.get(expr) {
            return *existing;
        }
        let res = match expr {
            Expr::Lit(l) => {
                let assign = self.fresh();
                res.push(NormAction::LetLit(assign, l.clone()));
                assign
            }
            Expr::Var(v) => *v,
            Expr::Call(f, children) => {
                let assign = self.fresh();
                let mut new_children = vec![];
                for child in children {
                    match child {
                        Expr::Var(v) => {
                            new_children.push(*v);
                        }
                        _ => {
                            let child = self.expr_to_flat_actions(child, res, memo);
                            new_children.push(child);
                        }
                    }
                }
                let result = NormExpr::Call(*f, new_children);
                let result_expr = result.to_expr();
                if let Some(existing) = memo.get(&result_expr) {
                    *existing
                } else {
                    memo.insert(result_expr.clone(), assign);
                    res.push(NormAction::Let(assign, result));
                    assign
                }
            }
        };
        memo.insert(expr.clone(), res);
        res
    }

    pub fn parse_program(&self, input: &str) -> Result<Vec<Command>, Error> {
        Ok(self
            .parser
            .parse(input)
            .map_err(|e| e.map_token(|tok| tok.to_string()))?)
    }

    pub fn declare(&mut self, name: Symbol, sort: Symbol) -> Vec<NCommand> {
        let fresh = self.fresh();
        vec![
            NCommand::Function(NormFunctionDecl {
                name: fresh,
                schema: Schema {
                    input: vec![],
                    output: sort,
                },
                default: None,
                merge: None,
                merge_action: vec![],
                cost: None,
                unextractable: false,
            }),
            NCommand::NormAction(NormAction::Let(name, NormExpr::Call(fresh, vec![]))),
        ]
    }

    pub fn desugar_function(&mut self, fdecl: &FunctionDecl) -> Vec<NCommand> {
        let mut res = vec![];
        let schema = if fdecl.schema.output.as_str() == UNIT_SYM {
            let fresh_sort = self.fresh();
            res.push(NCommand::Sort(fresh_sort, None));
            Schema {
                input: fdecl.schema.input.clone(),
                output: fresh_sort,
            }
        } else {
            fdecl.schema.clone()
        };
        res.push(NCommand::Function(NormFunctionDecl {
            name: fdecl.name,
            schema,
            default: fdecl.default.clone(),
            merge: fdecl.merge.clone(),
            merge_action: flatten_actions(&fdecl.merge_action, self),
            cost: fdecl.cost,
            unextractable: fdecl.unextractable,
        }));
        res
    }

    fn desugar_get_proof(&mut self, query: &Vec<Fact>) -> Result<Vec<NCommand>, Error> {
        let proof_ruleset = self.fresh().as_str();
        let result_sort = self.fresh().as_str();
        let result_func = self.fresh().as_str();
        let query_str = ListDisplay(query, " ");
        desugar_commands(
            self.parse_program(&format!(
                "
        (check {query_str})
        (ruleset {proof_ruleset})
        (sort {result_sort})
        (function {result_func} () {result_sort})
        (rule ({query_str})
              (({result_func}))
              :ruleset {proof_ruleset})
        (run {proof_ruleset} 1)
        (lookup-proof ({result_func}))
        ",
            ))
            .unwrap(),
            self,
            false,
            false,
        )
        .map(|cmds| cmds.into_iter().map(|cmd| cmd.command).collect())
    }
}
