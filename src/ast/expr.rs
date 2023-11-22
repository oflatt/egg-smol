use crate::{typecheck::ResolvedCall, *};
use ordered_float::OrderedFloat;

use std::fmt::Display;

use super::ToSexp;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Literal {
    Int(i64),
    F64(OrderedFloat<f64>),
    String(Symbol),
    Bool(bool),
    Unit,
}

macro_rules! impl_from {
    ($ctor:ident($t:ty)) => {
        impl From<Literal> for $t {
            fn from(literal: Literal) -> Self {
                match literal {
                    Literal::$ctor(t) => t,
                    #[allow(unreachable_patterns)]
                    _ => panic!("Expected {}, got {literal}", stringify!($ctor)),
                }
            }
        }

        impl From<$t> for Literal {
            fn from(t: $t) -> Self {
                Literal::$ctor(t)
            }
        }
    };
}

impl_from!(Int(i64));
impl_from!(F64(OrderedFloat<f64>));
impl_from!(String(Symbol));

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Literal::Int(i) => Display::fmt(i, f),
            Literal::F64(n) => {
                // need to display with decimal if there is none
                let str = n.to_string();
                if let Ok(_num) = str.parse::<i64>() {
                    write!(f, "{}.0", str)
                } else {
                    write!(f, "{}", str)
                }
            }
            Literal::Bool(b) => Display::fmt(b, f),
            Literal::String(s) => write!(f, "\"{}\"", s),
            Literal::Unit => write!(f, "()"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedVar {
    pub name: Symbol,
    pub sort: ArcSort,
}

impl Display for ResolvedVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl ToSexp for ResolvedVar {
    fn to_sexp(&self) -> Sexp {
        Sexp::Symbol(self.name.to_string())
    }
}

// TODO rename to Expr
pub type UnresolvedExpr = Expr<Symbol, Symbol, ()>;
pub type ResolvedExpr = Expr<ResolvedCall, ResolvedVar, ()>;

// TODO rename to generic expr
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Expr<Head, Leaf, Ann> {
    Lit(Ann, Literal),
    Var(Ann, Leaf),
    // TODO make this its own type
    Call(Ann, Head, Vec<Self>),
}

// impl NormExpr {
//     pub fn to_expr(&self) -> Expr<Symbol, ()> {
//         match self {
//             NormExpr::Call(op, args) => {
//                 Expr::Call(*op, args.iter().map(|a| Expr::Var(*a)).collect())
//             }
//         }
//     }

//     pub(crate) fn map_def_use(
//         &self,
//         fvar: &mut impl FnMut(Symbol, bool) -> Symbol,
//         is_def: bool,
//     ) -> NormExpr {
//         match self {
//             NormExpr::Call(op, args) => {
//                 let args = args.iter().map(|a| fvar(*a, is_def)).collect();
//                 NormExpr::Call(*op, args)
//             }
//         }
//     }
// }

impl UnresolvedExpr {
    pub fn call(op: impl Into<Symbol>, children: impl IntoIterator<Item = Self>) -> Self {
        Self::Call((), op.into(), children.into_iter().collect())
    }

    pub fn lit(lit: impl Into<Literal>) -> Self {
        Self::Lit((), lit.into())
    }
}

impl<Head: Clone + Display, Leaf: Hash + Clone + Display + Eq, Ann: Clone> Expr<Head, Leaf, Ann> {
    pub fn is_var(&self) -> bool {
        matches!(self, Expr::Var(_, _))
    }

    pub fn get_var(&self) -> Option<Leaf> {
        match self {
            Expr::Var(ann, v) => Some(v.clone()),
            _ => None,
        }
    }

    fn children(&self) -> &[Self] {
        match self {
            Expr::Var(_, _) | Expr::Lit(_, _) => &[],
            Expr::Call(_, _, children) => children,
        }
    }

    pub fn ast_size(&self) -> usize {
        let mut size = 0;
        self.walk(&mut |_e| size += 1, &mut |_| {});
        size
    }

    pub fn walk(&self, pre: &mut impl FnMut(&Self), post: &mut impl FnMut(&Self)) {
        pre(self);
        self.children()
            .iter()
            .for_each(|child| child.walk(pre, post));
        post(self);
    }

    pub fn fold<Out>(&self, f: &mut impl FnMut(&Self, Vec<Out>) -> Out) -> Out {
        let ts = self.children().iter().map(|child| child.fold(f)).collect();
        f(self, ts)
    }

    pub fn map(&self, f: &mut impl FnMut(&Self) -> Self) -> Self {
        match self {
            Expr::Lit(..) => f(self),
            Expr::Var(..) => f(self),
            Expr::Call(ann, op, children) => {
                let children = children.iter().map(|c| c.map(f)).collect();
                f(&Expr::Call(ann.clone(), *op, children))
            }
        }
    }

    // TODO: refactor subst to take a canonicalizing function rather than hash map.
    pub fn subst(&self, canon: &HashMap<Leaf, Self>) -> Self {
        match self {
            Expr::Lit(ann, _lit) => self.clone(),
            Expr::Var(ann, v) => canon.get(v).cloned().unwrap_or_else(|| self.clone()),
            Expr::Call(ann, op, children) => {
                let children = children.iter().map(|c| c.subst(canon)).collect();
                Expr::Call(ann.clone(), *op, children)
            }
        }
    }

    pub fn vars(&self) -> impl Iterator<Item = Leaf> + '_ {
        let iterator: Box<dyn Iterator<Item = Leaf>> = match self {
            Expr::Lit(_ann, _l) => Box::new(std::iter::empty()),
            Expr::Var(_ann, v) => Box::new(std::iter::once(v.clone())),
            Expr::Call(_ann, _head, exprs) => Box::new(exprs.iter().flat_map(|e| e.vars())),
        };
        iterator
    }

    pub(crate) fn map_def_use(&self, fvar: &mut impl FnMut(Leaf) -> Leaf) -> Self {
        match self {
            Expr::Lit(ann, _) => self.clone(),
            Expr::Var(ann, v) => Expr::Var(ann.clone(), fvar(*v)),
            Expr::Call(ann, op, args) => {
                let args = args.iter().map(|a| a.map_def_use(fvar)).collect();
                Expr::Call(ann.clone(), *op, args)
            }
        }
    }
}

impl<Head: Display, Leaf: Display, Ann> Expr<Head, Leaf, Ann> {
    /// Converts this expression into a
    /// s-expression (symbolic expression).
    /// Example: `(Add (Add 2 3) 4)`
    pub fn to_sexp(&self) -> Sexp {
        let res = match self {
            Expr::Lit(ann, lit) => Sexp::Symbol(lit.to_string()),
            Expr::Var(ann, v) => Sexp::Symbol(v.to_string()),
            Expr::Call(ann, op, children) => Sexp::List(
                vec![Sexp::Symbol(op.to_string())]
                    .into_iter()
                    .chain(children.iter().map(|c| c.to_sexp()))
                    .collect(),
            ),
        };
        res
    }
}

// impl Display for NormExpr {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}", self.to_expr())
//     }
// }

impl<Head, Leaf, Ann> Display for Expr<Head, Leaf, Ann>
where
    Head: Display,
    Leaf: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sexp())
    }
}

// currently only used for testing, but no reason it couldn't be used elsewhere later
#[cfg(test)]
pub(crate) fn parse_expr(
    s: &str,
) -> Result<UnresolvedExpr, lalrpop_util::ParseError<usize, String, String>> {
    let parser = ast::parse::ExprParser::new();
    parser
        .parse(s)
        .map_err(|e| e.map_token(|tok| tok.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser_display_roundtrip() {
        let s = r#"(f (g a 3) 4.0 (H "hello"))"#;
        let e = parse_expr(s).unwrap();
        assert_eq!(format!("{}", e), s);
    }
}
