use std::fmt::{Display, Formatter};

use crate::{
    ast::{Expr, Literal},
    util::{HashMap, HashSet, IndexMap, ListDisplay},
    Symbol, Value, UNIT_SYM,
};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Lit(Literal),
    Var(Symbol),
    App(Symbol, Vec<Value>),
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
    // use the value as the id so that
    // the ordering between terms is preserved
    nodes: IndexMap<Value, Term>,
    hashcons: IndexMap<Term, Value>,
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
    pub fn lookup(&self, node: &Term) -> Value {
        *self.hashcons.get(node).unwrap_or_else(|| {
            panic!(
                "Term {:?} not found in hashcons. Did you forget to add it?",
                node
            )
        })
    }

    pub fn get(&self, id: Value) -> Term {
        self.nodes.get(&id).unwrap().clone()
    }

    pub fn make(&mut self, sym: Symbol, children: Vec<Term>, value: Value) -> Term {
        let node = Term::App(sym, children.iter().map(|c| self.lookup(c)).collect());

        self.add_node(&node, value);

        node
    }

    pub fn make_lit(&mut self, lit: Literal, value: Value) -> Term {
        let node = Term::Lit(lit);

        self.add_node(&node, value);

        node
    }

    pub fn lookup_term(&self, sym: Symbol, children: Vec<Term>) -> Term {
        let children = children.iter().map(|c| self.lookup(c)).collect::<Vec<_>>();
        let node = Term::App(sym, children);
        self.lookup(&node);
        node
    }

    fn add_node(&mut self, node: &Term, value: Value) {
        if self.hashcons.get(node).is_none() {
            assert!(self.nodes.insert(value, node.clone()).is_none());
            self.hashcons.insert(node.clone(), value);
        }
    }

    pub fn term_to_expr(&mut self, term: &Term) -> Expr {
        match term {
            Term::Lit(lit) => Expr::Lit(lit.clone()),
            Term::Var(v) => Expr::Var(*v),
            Term::App(op, args) => {
                let args = args
                    .iter()
                    .map(|a| {
                        let term = self.get(*a);
                        self.term_to_expr(&term)
                    })
                    .collect();
                Expr::Call(*op, args)
            }
        }
    }

    pub fn to_string(&self, term: &Term) -> String {
        let mut stored = HashMap::<Value, String>::default();
        let mut seen = HashSet::default();
        let id = self.lookup(term);
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
                Term::Var(v) => {
                    stored.insert(next, format!("{}", v));
                }
            }
        }

        stored.get(&id).unwrap().clone()
    }

    pub fn display_entry(&self, entry: &FunctionEntry) -> String {
        if entry.output == Term::App(Symbol::from(UNIT_SYM), vec![]) {
            format!(
                "({} {})",
                entry.name,
                ListDisplay(entry.inputs.iter().map(|t| self.to_string(t)), " "),
            )
        } else {
            format!(
                "({} {}) -> {}",
                entry.name,
                ListDisplay(entry.inputs.iter().map(|t| self.to_string(t)), " "),
                self.to_string(&entry.output)
            )
        }
    }
}
