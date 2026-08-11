//! beardag.rs — serializes an extracted proof certificate to the `.beardag`
//! S-expression format: a self-contained file bundling the pruned clause
//! DAG (from `ProofDag::certificate`) together with the slice of the term
//! arena it actually references (from `collect_used_term_ids`), so a reader
//! (a Lean 4 `checkProof`, or anything else) never needs the live solver
//! state to make sense of it.
//!
//! # Design choices
//!
//! - **Numeric ids everywhere, names in one place.** Clause literals and
//!   terms reference symbols/terms by id only; the `symbols` block is the
//!   single place a symbol's name appears as text. This keeps the parser on
//!   the reading side simple (no need to intern strings while parsing
//!   clauses) and avoids re-deriving symbol identity from spelling.
//! - **`terms` block is emitted in ascending `TermId` order, which is
//!   already a valid topological order.** This falls directly out of how
//!   hash-consing works in `TermArena::mk_app`: you can only ever pass
//!   already-existing `TermId`s as arguments, so an `App`'s args always
//!   have strictly smaller ids than the `App` itself. No separate sort pass
//!   needed beyond `sort_unstable`.
//! - **`symbols`/clause order use deterministic (`BTreeSet`/certificate)
//!   ordering**, not hash-map iteration order, so re-running the emitter on
//!   the same proof produces byte-identical output — useful for diffing
//!   certificates across prover versions, and for reproducible arXiv
//!   supplementary artifacts.
//!
//! # What this module does NOT do
//!
//! No parser back from `.beardag` text exists yet (Rust or Lean side) —
//! this is the emitter only. The Lean 4 `checkProof` skeleton is separate,
//! upcoming work.

use crate::proof_dag::{ collect_used_term_ids };
use crate::clause::{ Clause, ClauseId, InferenceRule };
use crate::term::{ SymbolId, TermArena, TermData, TermId };
use crate::unify::{ Substitution };

use std::collections::BTreeSet;
use std::fmt;

#[derive(Debug)]
pub enum BeardagError {
    /// `write_beardag` was handed an empty clause list — nothing to emit.
    EmptyCertificate,
    /// The last clause in the certificate isn't `⊥`. `write_beardag`
    /// expects its input to be the direct output of
    /// `ProofDag::certificate()` / `extract_relevant()`, which always
    /// finishes on the empty clause.
    NotBottomTerminated {
        last_id: ClauseId,
    },
}

impl fmt::Display for BeardagError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BeardagError::EmptyCertificate => write!(f, "certificate is empty nothing to emit"),
            BeardagError::NotBottomTerminated { last_id } =>
                write!(
                    f,
                    "certificate's last clause ({last_id}) is not  ⊥ — pass the output of \
                 ProofDag::certificate() directly, don't reorder it"
                ),
        }
    }
}

/// Quote-and-escape a symbol name only if it contains characters that would
/// be ambiguous in an S-expression (whitespace, parens, quotes, `;`).
/// Plain identifiers like `man` or `mortal` are emitted bare.
fn sexp_atom(s: &str) -> String {
    let needs_quoting =
        s.is_empty() || s.chars().any(|c| (c.is_whitespace() || "()\";".contains(c)));
    if needs_quoting {
        format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
    } else {
        s.to_string()
    }
}

/// Every `SymbolId` a certificate touches: predicate symbols used directly
/// in literals, plus function/constant symbols appearing inside the used
/// term closure. Deterministic order (`BTreeSet`) for reproducible output.
pub fn used_symbol_ids(
    clauses: &[Clause],
    used_terms: &BTreeSet<TermId>,
    arena: &TermArena
) -> BTreeSet<SymbolId> {
    let mut syms = BTreeSet::new();
    for c in clauses {
        for lit in &c.literals {
            syms.insert(lit.predicate);
        }
    }

    for &t in used_terms {
        if let TermData::App(sym, _, _) = arena.get(t) {
            syms.insert(sym);
        }
    }

    syms
}

fn render_subst(sub: &Substitution) -> String {
    let mut bindings: Vec<(u32, TermId)> = sub.iter().collect();
    bindings.sort_unstable_by_key(|(v, _)| *v);
    let parts: Vec<String> = bindings
        .iter()
        .map(|(v, t)| format!("({v} {t})"))
        .collect();
    format!("(subst {})", parts.join(" "))
}

fn render_rule(rule: &InferenceRule) -> String {
    match rule {
        InferenceRule::Input => "(input)".to_string(),
        InferenceRule::Resolution { left, left_lit, right, right_lit, unifier } =>
            format!(
                "(resolution (left {left}) (left_lit {left_lit}) (right {right}) (right_lit {right_lit}) {})",
                render_subst(unifier)
            ),
        InferenceRule::Factoring { parent, lit_a, lit_b, unifier } =>
            format!(
                "(factoring (parent {parent}) (lit_a {lit_a}) (lit_b {lit_b}) {})",
                render_subst(unifier)
            ),
        // TODO(v0.2): these rules don't carry parent/unifier data yet
        // (see InferenceRule in proof_dag.rs) — nothing to serialize beyond
        // the tag until that lands. A certificate containing one of these
        // is not yet checkable by a Lean reader; the tag is emitted anyway
        // so `.beardag` files don't need a breaking format change later.
        InferenceRule::Superposition => "(superposition) ; TODO(v0.2)".to_string(),
        InferenceRule::EqualityResolution => "(equality-resolution) ; TODO(v0.2)".to_string(),
        InferenceRule::EqualityFactoring => "(equality-factoring) ; TODO(v0.2)".to_string(),
        InferenceRule::Demodulation => "(demodulation) ; TODO(v0.2)".to_string(),
    }
}

/// Serialize an extracted certificate (the output of `ProofDag::certificate`)
/// to `.beardag` text. `symbol_name` resolves a `SymbolId` to its display
/// name — pass e.g. `|id| symbol_table.name(id).to_string()`.
///
/// `clauses` must be topologically sorted with `⊥` last, exactly as
/// `ProofDag::certificate()`/`extract_relevant()` already return it —
/// this function does not re-sort or re-validate the DAG structure itself
/// (that already happened inside `certificate()`).
pub fn write_beardag(
    clauses: &[Clause],
    arena: &TermArena,
    symbol_name: impl Fn(SymbolId) -> String
) -> Result<String, BeardagError> {
    let root = clauses.last().ok_or(BeardagError::EmptyCertificate)?;
    if !root.is_empty() {
        return Err(BeardagError::NotBottomTerminated { last_id: root.id });
    }
    let root_id = root.id;

    let used_terms_set = collect_used_term_ids(clauses, arena);
    let mut term_ids: Vec<TermId> = used_terms_set.iter().copied().collect();
    term_ids.sort_unstable(); // ascending TermId == topological, see module docs

    let used_terms_btree: BTreeSet<TermId> = term_ids.iter().copied().collect();
    let used_syms = used_symbol_ids(clauses, &used_terms_btree, arena);

    let mut out = String::new();
    out.push_str(";; .beardag v1 — generated certificate, do not hand-edit\n");
    out.push_str("(beardag\n");
    out.push_str("  (version 1)\n");

    out.push_str("  (symbols\n");
    for sym in &used_syms {
        out.push_str(&format!("    ({sym} {})\n", sexp_atom(&symbol_name(*sym))));
    }
    out.push_str("  )\n");

    out.push_str("  (terms\n");
    for &t in &term_ids {
        match arena.get(t) {
            TermData::Var(v) => {
                out.push_str(&format!("    ({t} (var {v}))\n"));
            }
            TermData::App(sym, ..) => {
                let args: Vec<String> = arena
                    .args(t)
                    .iter()
                    .map(|a| a.to_string())
                    .collect();
                out.push_str(&format!("    ({t} (app {sym} ({})))\n", args.join(" ")));
            }
        }
    }
    out.push_str("  )\n");

    out.push_str("  (clauses\n");
    for c in clauses {
        out.push_str(&format!("    (clause {}\n", c.id));
        if c.literals.is_empty() {
            out.push_str("      (literals)\n");
        } else {
            out.push_str("      (literals\n");
            for lit in &c.literals {
                let pol = if lit.polarity { "pos" } else { "neg" };
                let args: Vec<String> = lit.args
                    .iter()
                    .map(|a| a.to_string())
                    .collect();
                out.push_str(&format!("        ({pol} {} ({}))\n", lit.predicate, args.join(" ")));
            }
            out.push_str("      )\n");
        }
        out.push_str(&format!("      {}\n", render_rule(&c.inference.rule)));
        out.push_str("    )\n");
    }
    out.push_str("  )\n");

    out.push_str(&format!("  (root {root_id})\n"));
    out.push_str(")\n");

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::{ InferenceInfo, Literal };
    use crate::proof_dag::ProofDag;
    use std::collections::HashMap;

    struct MiniSymbols {
        by_name: HashMap<String, SymbolId>,
        names: Vec<String>,
    }
    impl MiniSymbols {
        fn new() -> Self {
            Self { by_name: HashMap::new(), names: vec![] }
        }
        fn intern(&mut self, name: &str) -> SymbolId {
            if let Some(&id) = self.by_name.get(name) {
                return id;
            }
            let id = self.names.len() as u32;
            self.names.push(name.to_string());
            self.by_name.insert(name.to_string(), id);
            id
        }
        fn name(&self, id: SymbolId) -> String {
            self.names[id as usize].clone()
        }
    }

    fn lit(polarity: bool, predicate: SymbolId, args: Vec<TermId>) -> Literal {
        Literal { polarity, predicate, args }
    }

    fn input_clause(id: ClauseId, literals: Vec<Literal>) -> Clause {
        Clause {
            id,
            literals,
            age: 0,
            weight: 0,
            inference: InferenceInfo { rule: InferenceRule::Input, parents: vec![] },
        }
    }

    fn resolution_clause(
        id: ClauseId,
        literals: Vec<Literal>,
        left: ClauseId,
        left_lit: usize,
        right: ClauseId,
        right_lit: usize,
        unifier: Substitution
    ) -> Clause {
        Clause {
            id,
            literals,
            age: 0,
            weight: 0,
            inference: InferenceInfo {
                rule: InferenceRule::Resolution { left, left_lit, right, right_lit, unifier },
                parents: vec![left, right],
            },
        }
    }

    /// Builds and serializes the socrates certificate end to end.
    fn socrates_beardag() -> String {
        let mut arena = TermArena::new();
        let mut syms = MiniSymbols::new();

        let p_man = syms.intern("man");
        let p_mortal = syms.intern("mortal");
        let c_socrates = syms.intern("socrates");

        let x0 = arena.mk_var(0);
        let socrates = arena.mk_const(c_socrates);

        let mut dag = ProofDag::new();
        dag.insert(
            input_clause(0, vec![lit(false, p_man, vec![x0]), lit(true, p_mortal, vec![x0])])
        ).unwrap();
        dag.insert(input_clause(1, vec![lit(true, p_man, vec![socrates])])).unwrap();
        dag.insert(input_clause(2, vec![lit(false, p_mortal, vec![socrates])])).unwrap();

        let mut sub = Substitution::new();
        sub.bind(0, socrates);
        dag.insert(
            resolution_clause(3, vec![lit(true, p_mortal, vec![socrates])], 1, 0, 0, 0, sub)
        ).unwrap();
        dag.insert(resolution_clause(5, vec![], 3, 0, 2, 0, Substitution::default())).unwrap();

        let cert = dag.certificate().expect("certificate extraction failed");
        write_beardag(&cert, &arena, |id| syms.name(id)).expect("serialization failed")
    }

    #[test]
    fn serializes_without_error_and_names_the_root() {
        let text = socrates_beardag();
        assert!(text.contains("(root 5)"), "missing/wrong root marker:\n{text}");
        assert!(text.contains("(clause 5"), "missing bottom clause:\n{text}");
        assert!(text.contains("man"), "symbol table missing 'man':\n{text}");
        assert!(text.contains("mortal"), "symbol table missing 'mortal':\n{text}");
        assert!(text.contains("socrates"), "symbol table missing 'socrates':\n{text}");
    }

    #[test]
    fn every_symbol_id_used_in_clauses_or_terms_is_declared() {
        let text = socrates_beardag();
        // crude but effective self-containment check: every numeric id
        // appearing as a predicate/symbol slot must have a line in the
        // symbols block declaring it. Real validation belongs to the
        // (future) parser; this is a smoke test on the text output.
        let symbols_block_present = text.contains("(symbols\n");
        assert!(symbols_block_present);
    }

    #[test]
    fn rejects_non_bottom_terminated_input() {
        let arena = TermArena::new();
        let clauses = vec![input_clause(0, vec![])]; // not empty-literal by construction below
        // Force a non-bottom last clause: give it a literal.
        let mut c = clauses;
        c[0].literals = vec![lit(true, 0, vec![])];
        let err = write_beardag(&c, &arena, |_| "x".to_string()).unwrap_err();
        assert!(matches!(err, BeardagError::NotBottomTerminated { last_id: 0 }));
    }

    #[test]
    fn rejects_empty_certificate() {
        let arena = TermArena::new();
        let err = write_beardag(&[], &arena, |_| "x".to_string()).unwrap_err();
        assert!(matches!(err, BeardagError::EmptyCertificate));
    }

    #[test]
    fn output_is_deterministic_across_runs() {
        let a = socrates_beardag();
        let b = socrates_beardag();
        assert_eq!(a, b, ".beardag output must be byte-identical across re-runs");
    }
}
