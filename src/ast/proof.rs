enum Term {
    Lit(Literal),
    App(Symbol, Vec<Term>),
}

enum ProofFact {
    Equality(Term, Term),
    TableEntry(Symbol, Vec<Term>),
    Term(Term),
}

enum Proof {
    OriginalFact(ProofFact),
    DerivedEntry {
        fact: ProofFact,
        rule_name: String,
        proof_per_fact: Vec<Proof>,
    },
}
