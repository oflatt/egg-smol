use crate::{
    ast::{Expr, Literal},
    util::{HashMap, HashSet, IndexMap, ListDisplay},
    EGraph, Symbol, Value, UNIT_SYM,
};

#[derive(Clone, PartialEq, Eq, Debug, Hash, Copy)]
pub enum TermId {
    Value(Value),
    Num(usize),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Lit(Literal),
    App(Symbol, Vec<TermId>),
}

/// Some functions in egglog are not datatypes
/// because they have a merge function.
/// A Term is built from only datatypes, so it cannot
/// represent the entries in these tables.
/// So we have this datatype for that
pub struct FunctionEntry {
    pub name: Symbol,
    pub inputs: Vec<Term>,
    pub output: Term,
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct TermDag {
    // use the TermId as the id so that
    // the ordering between terms is preserved
    nodes: IndexMap<TermId, Term>,
    hashcons: IndexMap<Term, TermId>,
    fresh_id_counter: usize,
}

#[macro_export]
macro_rules! match_term_app {
    ($e:expr; { $(
        ($head:expr, $args:pat) => $body:expr $(,)?
    ),*}) => {
        match $e {
            Term::App(head, args) => {
                $(
                    if head.as_str() == $head {
                        match args.as_slice() {
                            $args => $body,
                            _ => panic!("arg mismatch"),
                        }
                    } else
                )* {
                    panic!("Failed to match any of the heads of the patterns. Got: {}", head);
                }
            }
            _ => panic!("not an app")
        }
    }
}

impl TermDag {
    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    // users can't construct a termnode, so just
    // look it up
    pub fn get_id(&self, node: &Term) -> TermId {
        *self.hashcons.get(node).unwrap_or_else(|| {
            panic!(
                "Term {:?} not found in hashcons. Did you forget to add it?",
                node
            )
        })
    }

    pub fn get_term(&self, id: TermId) -> Term {
        self.nodes.get(&id).unwrap().clone()
    }

    /// Make a term from a symbol and a list of children.
    /// Optionally, provide an egraph. When an egraph
    /// is provided, the identifiers of terms which also
    /// appear in the egraph are used.
    /// This preserves the ordering on terms in the egraph.
    pub fn make(&mut self, sym: Symbol, children: Vec<Term>, egraph: Option<&EGraph>) -> Term {
        let node = Term::App(sym, children.iter().map(|c| self.get_id(c)).collect());

        self.add_node(&node, egraph);

        node
    }

    pub fn make_lit(&mut self, lit: Literal, egraph: Option<&EGraph>) -> Term {
        let node = Term::Lit(lit);

        self.add_node(&node, egraph);

        node
    }

    pub fn lookup_term(&self, sym: Symbol, children: Vec<Term>) -> Term {
        let children = children.iter().map(|c| self.get_id(c)).collect::<Vec<_>>();
        let node = Term::App(sym, children);
        self.get_id(&node);
        node
    }

    fn add_node(&mut self, node: &Term, egraph: Option<&EGraph>) -> TermId {
        /*if node
            == &Term::App(
                "AddT___".into(),
                vec![Value {
                    tag: "Expr".into(),
                    bits: 58,
                }],
            )
        {
            panic!("here");
        }*/
        let egraph_id = if let Some(egraph) = egraph {
            match node {
                Term::App(sym, children) => {
                    if children
                        .iter()
                        .all(|child| matches!(child, TermId::Value(_)))
                    {
                        let children = children
                            .iter()
                            .map(|child| match child {
                                TermId::Value(v) => *v,
                                _ => panic!("not a value"),
                            })
                            .collect::<Vec<_>>();
                        if let Some(func) = egraph.functions.get(sym) {
                            func.nodes.get(&children).map(|entry| entry.value)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                Term::Lit(lit) => Some(egraph.eval_lit(lit)),
            }
        } else {
            None
        };
        if let Some(existing) = self.hashcons.get(node) {
            if let Some(egraph_val) = egraph_id {
                assert_eq!(
                    *existing,
                    TermId::Value(egraph_val),
                    "Tried to add term {:?} again with different id.",
                    node
                );
            }
            *existing
        } else {
            let new_id = if let Some(egraph_val) = egraph_id {
                TermId::Value(egraph_val)
            } else {
                let id = TermId::Num(self.fresh_id_counter);
                self.fresh_id_counter += 1;
                id
            };
            let old = self.nodes.insert(new_id, node.clone());
            self.hashcons.insert(node.clone(), new_id);
            assert!(
                old.is_none(),
                "Tried to add node with duplicate id.\nOld term: {:?}\nNew term: {:?}\n
                Old: {}\n
                New: {}\n",
                old.clone().unwrap(),
                node,
                self.to_string(&old.unwrap(), &true),
                self.to_string(&node, &true),
            );
            new_id
        }
    }

    pub fn term_to_expr(&mut self, term: &Term) -> Expr {
        match term {
            Term::Lit(lit) => Expr::Lit(lit.clone()),
            Term::App(op, args) => {
                let args = args
                    .iter()
                    .map(|a| {
                        let term = self.get_term(*a);
                        self.term_to_expr(&term)
                    })
                    .collect();
                Expr::Call(*op, args)
            }
        }
    }

    fn term_id_to_string(&self, val: &TermId) -> String {
        match val {
            TermId::Value(v) => format!("Tag: {} Bits: {}", v.tag, v.bits),
            TermId::Num(n) => format!("Num: {}", n),
        }
    }

    pub fn to_string(&self, term: &Term, print_tree: &bool) -> String {
        if *print_tree {
            // Tree output
            let mut stored = HashMap::<TermId, String>::default();
            let mut seen = HashSet::default();
            let id = self.get_id(term);
            // use a stack to avoid stack overflow
            let mut stack = vec![id];
            while !stack.is_empty() {
                let next = stack.pop().unwrap();

                match self.nodes.get(&next).unwrap().clone() {
                    Term::App(name, children) => {
                        if seen.contains(&next) {
                            let mut str = String::new();
                            str.push_str(&format!("({}", name));
                            for c in children.iter() {
                                str.push_str(&format!(" {}", stored[c]));
                            }
                            str.push(')');
                            stored.insert(next, str);
                        } else {
                            seen.insert(next);
                            stack.push(next);
                            for c in children.iter().rev() {
                                stack.push(*c);
                            }
                        }
                    }
                    Term::Lit(lit) => {
                        stored.insert(next, format!("{}", lit));
                    }
                }
            }

            stored.get(&id).unwrap().clone()
        } else {
            // DAG output
            let mut stored: HashMap<TermId, String> = HashMap::default();
            let mut adj_list: HashMap<TermId, Vec<i32>> = HashMap::default();
            let mut seen = HashSet::default();
            let mut term_id_map: HashMap<TermId, i32> = HashMap::default();
            let mut term_id_insertion_order: Vec<TermId> = Vec::default();
            let mut value_map = HashMap::<i32, TermId>::default();
            let mut counter = 0;
            let id = self.get_id(term);
            let mut stack = vec![id];

            while !stack.is_empty() {
                let next: TermId = stack.pop().unwrap();
                if !seen.contains(&next) {
                    // Give a homemade id number to it
                    term_id_insertion_order.push(next);
                    term_id_map.insert(next, counter);
                    counter = counter + 1;
                    if let TermId::Value(v) = next {
                        value_map.insert(v.bits as i32, next);
                    }
                }
                if let Term::App(_, children) = self.nodes.get(&next).unwrap().clone() {
                    if !seen.contains(&next) {
                        // Add the children to get numbered and then revisit this node
                        seen.insert(next);
                        for c in children.iter().rev() {
                            stack.push(*c);
                        }
                    }
                }
            }

            let mut values = value_map.keys().collect::<Vec<_>>();
            let mut homemade_value_ids = value_map
                .iter()
                .map(|(k, v)| *term_id_map.get(v).unwrap())
                .collect::<Vec<_>>();

            values.sort();
            homemade_value_ids.sort();

            for (i, v) in values.iter().enumerate() {
                term_id_map.insert(value_map[*v], homemade_value_ids[i]);
            }

            seen.clear();
            stack = vec![id];

            // Construct the new IDs and construct the adjacency lis
            while !stack.is_empty() {
                let next: TermId = stack.pop().unwrap();
                match self.nodes.get(&next).unwrap().clone() {
                    Term::App(name, children) => {
                        if !seen.contains(&next) {
                            // Add the children to get numbered and then revisit this node
                            seen.insert(next);
                            stack.push(next);
                            for c in children.iter().rev() {
                                stack.push(*c);
                            }
                        } else {
                            // Construct the string for this node
                            let mut str = String::new();
                            let mut edges: Vec<i32> = Vec::default();
                            str.push_str(&format!(
                                "(Term: {}, Value: ({}",
                                term_id_map.get(&next).unwrap().to_string().as_str(),
                                name
                            ));
                            for c in children.iter() {
                                str.push_str(&format!(
                                    " (Term: {})",
                                    term_id_map.get(c).unwrap().to_string().as_str()
                                ));
                                edges.push(*term_id_map.get(c).unwrap());
                            }
                            str.push_str("))");
                            adj_list.insert(next, edges);
                            stored.insert(next, str);
                        }
                    }
                    Term::Lit(lit) => {
                        adj_list.insert(next, Vec::default());
                        stored.insert(
                            next,
                            format!(
                                "(Term: {}, Value: {})",
                                term_id_map.get(&next).unwrap().to_string().as_str(),
                                lit
                            ),
                        );
                    }
                }
            }

            // Construct the string
            let mut str = String::new();
            str.push('\n');
            for id in term_id_insertion_order.iter() {
                str.push_str(stored.get(id).unwrap());
                str.push('\n');
            }
            str
        }
    }

    pub fn display_entry(&self, entry: &FunctionEntry) -> String {
        if entry.output == Term::App(Symbol::from(UNIT_SYM), vec![]) {
            format!(
                "({} {})",
                entry.name,
                ListDisplay(entry.inputs.iter().map(|t| self.to_string(t, &true)), " "),
            )
        } else {
            format!(
                "({} {}) -> {}",
                entry.name,
                ListDisplay(entry.inputs.iter().map(|t| self.to_string(t, &true)), " "),
                self.to_string(&entry.output, &true)
            )
        }
    }
}
