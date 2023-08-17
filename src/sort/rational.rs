use num_integer::Roots;
use num_traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, One, Signed, ToPrimitive, Zero};
use std::sync::Mutex;

pub type Rational = num_rational::Rational64;
use crate::{ast::Literal, util::IndexSet};

use super::*;

#[derive(Debug)]
pub struct RationalSort {
    name: Symbol,
    rats: Mutex<IndexSet<Rational>>,
}

impl RationalSort {
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            rats: Default::default(),
        }
    }
}

impl Sort for RationalSort {
    fn name(&self) -> Symbol {
        self.name
    }

    fn as_arc_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync + 'static> {
        self
    }

    #[rustfmt::skip]
    fn register_primitives(self: Arc<Self>, eg: &mut TypeInfo) {
        type Opt<T=()> = Option<T>;

        // TODO we can't have primitives take borrows just yet, since it
        // requires returning a reference to the locked sort
        add_primitives!(eg, "+" = |a: Rational, b: Rational| -> Opt<Rational> { a.checked_add(&b) });
        add_primitives!(eg, "-" = |a: Rational, b: Rational| -> Opt<Rational> { a.checked_sub(&b) });
        add_primitives!(eg, "*" = |a: Rational, b: Rational| -> Opt<Rational> { a.checked_mul(&b) });
        add_primitives!(eg, "/" = |a: Rational, b: Rational| -> Opt<Rational> { a.checked_div(&b) });

        add_primitives!(eg, "min" = |a: Rational, b: Rational| -> Rational { a.min(b) });
        add_primitives!(eg, "max" = |a: Rational, b: Rational| -> Rational { a.max(b) });
        add_primitives!(eg, "neg" = |a: Rational| -> Rational { -a });
        add_primitives!(eg, "abs" = |a: Rational| -> Rational { a.abs() });
        add_primitives!(eg, "floor" = |a: Rational| -> Rational { a.floor() });
        add_primitives!(eg, "ceil" = |a: Rational| -> Rational { a.ceil() });
        add_primitives!(eg, "round" = |a: Rational| -> Rational { a.round() });
        add_primitives!(eg, "rational" = |a: i64, b: i64| -> Rational { Rational::new(a, b) });
        add_primitives!(eg, "to-f64" = |a: Rational| -> f64 { a.to_f64().unwrap() });

        add_primitives!(eg, "pow" = |a: Rational, b: Rational| -> Option<Rational> {
            if a.is_zero() {
                if b.is_positive() {
                    Some(Rational::zero())
                } else {
                    None
                }
            } else if b.is_zero() {
                Some(Rational::one())
            } else if let Some(b) = b.to_i64() {
                if let Ok(b) = usize::try_from(b) {
                    num_traits::checked_pow(a, b)
                } else {
                    // TODO handle negative powers
                    None
                }
            } else {
                None
            }
        });
        add_primitives!(eg, "log" = |a: Rational| -> Option<Rational> {
            if a.is_one() {
                Some(Rational::zero())
            } else {
                todo!()
            }
        });
        add_primitives!(eg, "sqrt" = |a: Rational| -> Option<Rational> {
            if a.numer().is_positive() && a.denom().is_positive() {
                let s1 = a.numer().sqrt();
                let s2 = a.denom().sqrt();
                let is_perfect = &(s1 * s1) == a.numer() && &(s2 * s2) == a.denom();
                if is_perfect {
                    Some(Rational::new(s1, s2))
                } else {
                    None
                }
            } else {
                None
            }
        });
        add_primitives!(eg, "cbrt" = |a: Rational| -> Option<Rational> {
            if a.is_one() {
                Some(Rational::one())
            } else {
                todo!()
            }
        });

        add_primitives!(eg, "<" = |a: Rational, b: Rational| -> Opt { if a < b {Some(())} else {None} }); 
        add_primitives!(eg, ">" = |a: Rational, b: Rational| -> Opt { if a > b {Some(())} else {None} }); 
        add_primitives!(eg, "<=" = |a: Rational, b: Rational| -> Opt { if a <= b {Some(())} else {None} }); 
        add_primitives!(eg, ">=" = |a: Rational, b: Rational| -> Opt { if a >= b {Some(())} else {None} }); 
   }
    fn make_expr(&self, egraph: &EGraph, value: Value, termdag: &mut TermDag) -> Term {
        assert!(value.tag == self.name());
        let rat = Rational::load(self, &value);
        let numer = *rat.numer();
        let denom = *rat.denom();
        let numer_lit = Literal::Int(numer);
        let denom_lit = Literal::Int(denom);
        let numer_val = egraph.eval_lit(&numer_lit);
        let denom_val = egraph.eval_lit(&denom_lit);
        let numer_term = termdag.make_lit(numer_lit, Some(egraph));
        let denom_term = termdag.make_lit(denom_lit, Some(egraph));

        termdag.make(
            "rational".into(),
            vec![numer_term, denom_term],
            Some(egraph),
        )
    }
}

impl FromSort for Rational {
    type Sort = RationalSort;
    fn load(sort: &Self::Sort, value: &Value) -> Self {
        let i = value.bits as usize;
        *sort.rats.lock().unwrap().get_index(i).unwrap()
    }
}

impl IntoSort for Rational {
    type Sort = RationalSort;
    fn store(self, sort: &Self::Sort) -> Option<Value> {
        let (i, _) = sort.rats.lock().unwrap().insert_full(self);
        Some(Value {
            tag: sort.name,
            bits: i as u64,
        })
    }
}
