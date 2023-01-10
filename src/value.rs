use std::num::NonZeroU32;

use crate::{ast::Symbol, Id, F64};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
// FIXME this shouldn't be pub
pub struct Value {
    pub tag: Symbol,
    pub bits: u64,
}

impl Value {
    pub fn unit() -> Self {
        Value {
            tag: Symbol::new("Unit"),
            bits: 0,
        }
    }

    pub fn fake() -> Self {
        Value {
            tag: Symbol::new("__bogus__"),
            bits: 1234567890,
        }
    }

    pub fn from_id(tag: Symbol, id: Id) -> Self {
        Value {
            tag,
            bits: usize::from(id) as u64,
        }
    }
}

impl From<i64> for Value {
    fn from(i: i64) -> Self {
        Self {
            tag: Symbol::from("i64"),
            bits: i as u64,
        }
    }
}

impl From<f64> for Value {
    fn from(f: f64) -> Self {
        Self {
            tag: Symbol::from("f64"),
            bits: f.to_bits(),
        }
    }
}

impl From<F64> for Value {
    fn from(f: F64) -> Self {
        Self {
            tag: Symbol::from("f64"),
            bits: f.to_bits(),
        }
    }
}

impl From<Symbol> for Value {
    fn from(s: Symbol) -> Self {
        Self {
            tag: Symbol::from("String"),
            bits: NonZeroU32::from(s).get().into(),
        }
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Self {
            tag: Symbol::from("bool"),
            bits: b as u64,
        }
    }
}