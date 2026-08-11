//! Inference rules: **Resolution** and **Factoring** (v0.1). `Superposition`,
//! `EqualityResolution`, `EqualityFactoring`, `Demodulation` follow in v0.2
//! once equality reasoning lands (README §2).
//!
//! This module also owns `VarGen` + `rename_apart` — the "variable renaming
//! apart" mechanism that is MANDATORY before resolving between TWO different
//! clauses. Why: `VarId` is only unique within the scope of a single clause
//! (see the note on `term::VarId`), so two independent clauses can easily
//! both have a "variable 0" that mean completely unrelated things. Without
//! rename-apart, unification between clauses could wrongly treat two
//! unrelated variables as if they were the same one.
//!
//! `Factoring`, by contrast, operates WITHIN one clause — its variables are
//! already consistently scoped, so it does NOT need rename-apart.

use std::collections::HashSet;

use crate::clause::{ Clause, InferenceInfo, InferenceRule, Literal };
use crate::term::{ TermArena, TermData, TermId, VarId };
use crate::unify::{ unify_literals, Substitution };

/// Generates variable ids that are unique GLOBALLY across one whole proof
/// session (unlike raw `VarId`, which is only scoped per-clause). `resolve`
/// uses ONE shared `VarGen` to rename-apart BOTH of its input clauses, which
/// is what guarantees the two renamed copies can never overlap.
#[derive(Debug, Default)]
pub struct VarGen {
    next: VarId,
}

impl VarGen {
    pub fn new() -> Self {
        Self { next: 0 }
    }

    /// Hand out a variable id that has never been returned by this `VarGen`
    /// before (whether it ended up being "used" or "burned" — see
    /// `rename_apart`'s collision-avoidance loop, which calls this multiple
    /// times per variable in the rare case of a collision, and NEVER
    /// re-emits a value it already handed out, even a skipped one).
    ///
    /// **Complexity:** O(1).
    pub fn fresh(&mut self) -> VarId {
        let v = self.next;
        self.next += 1;
        v
    }
}

/// Recursively collect every distinct `VarId` appearing anywhere inside
/// `term` into `out`.
///
/// **Algorithm:** plain DFS — `Var` contributes itself, `App` recurses into
/// every argument.
///
/// **Complexity:** O(size of `term`).
fn collect_vars(term: TermId, arena: &TermArena, out: &mut HashSet<VarId>) {
    match arena.get(term) {
        TermData::Var(v) => {
            out.insert(v);
        }
        TermData::App(..) => {
            for &a in arena.args(term) {
                collect_vars(a, arena, out);
            }
        }
    }
}

/// Replace every variable in `literals` with a fresh variable from
/// `var_gen`.
///
/// **Algorithm:**
/// 1. Scan every literal's arguments to collect the FULL set of distinct
///    variables used anywhere in this clause (`collect_vars`).
/// 2. For each of those variables, pull a fresh id from `var_gen` and build
///    a `Substitution` mapping old-var -> fresh-var-as-a-term.
///    **Collision-avoidance loop:** if the fresh id happens to already be
///    one of THIS clause's own variable ids (most commonly: `var_gen` just
///    started at 0 and the clause also happens to use variable 0), draw
///    another fresh id instead. See the big comment inline below for why
///    this exists — it's not defensive paranoia, it's a fix for a real bug
///    that was hit during development (`X -> X` self-binding causing
///    `Substitution::resolve` to loop forever).
/// 3. Apply that ONE substitution (built once, up front, not per-literal) to
///    every literal via the existing `Substitution::apply` machinery —
///    renaming is implemented as a special case of substitution, not a
///    separate mechanism. Because the mapping is built once for the whole
///    clause, a variable appearing in multiple literals (e.g. `X` in both
///    `P(X)` and `Q(X)`) is guaranteed to map to the SAME fresh variable in
///    both places.
///
/// **Complexity:** O(size of `literals`) to collect variables, O(size of
/// `literals`) again to apply the substitution — so O(clause size) overall,
/// plus O(1) amortized per variable for the collision-avoidance loop (it
/// essentially never actually loops more than once or twice in practice).
pub fn rename_apart(
    literals: &[Literal],
    var_gen: &mut VarGen,
    arena: &mut TermArena
) -> Vec<Literal> {
    let mut vars = HashSet::new();
    for lit in literals {
        for &t in &lit.args {
            collect_vars(t, arena, &mut vars);
        }
    }

    let mut subst = Substitution::new();
    for &v in &vars {
        // Pull a fresh id from `var_gen`. If it happens to collide with one
        // of THIS clause's own original variables (including `v` itself —
        // the most common case: `var_gen` starts fresh at 0 and this clause
        // also happens to use variable 0), discard it and pull again.
        // `var_gen` never re-emits a value handed out this way, so this
        // does not violate the disjointness guarantee between separate
        // `rename_apart` calls (see the test
        // `rename_apart_produces_disjoint_variables_across_two_calls`).
        //
        // WITHOUT this check, `v -> mk_var(v)` could be generated (a
        // binding to ITSELF) and make `Substitution::resolve` infinite-loop
        // — this actually happened once, hence the explicit comment.
        let mut fresh = var_gen.fresh();
        while vars.contains(&fresh) {
            fresh = var_gen.fresh();
        }
        let fresh_term = arena.mk_var(fresh);
        subst.bind(v, fresh_term);
    }

    literals
        .iter()
        .map(|lit| apply_to_literal(lit, &subst, arena))
        .collect()
}

/// Apply `subst` to every argument of one literal, building a new `Literal`
/// (polarity/predicate copied as-is, only `args` changes).
fn apply_to_literal(lit: &Literal, subst: &Substitution, arena: &mut TermArena) -> Literal {
    let new_args = lit.args
        .iter()
        .map(|&t| subst.apply(t, arena))
        .collect();
    Literal { polarity: lit.polarity, predicate: lit.predicate, args: new_args }
}

/// The result of one inference: the new clause's literals + its provenance.
/// NOT yet inserted into a `ClauseStore` — that's the given-clause loop's
/// job (`saturation.rs`), which may end up discarding some results (e.g. due
/// to subsumption/tautology deletion, v0.2) before they're actually stored.
pub type InferenceResult = (Vec<Literal>, InferenceInfo);

/// Try Resolution between EVERY pair of literals (one from `c1`, one from
/// `c2`) with opposite polarity and matching predicate. Returns ALL
/// resolvents that successfully form — zero, one, or many, since a clause
/// can have multiple literals sharing a predicate.
///
/// `c1` and `c2` are rename-apart'd internally first, using the SAME
/// `var_gen` — this is what guarantees their variables can never collide,
/// even though their raw `VarId`s both originally started counting from 0.
///
/// **Algorithm:**
/// 1. `rename_apart` both input clauses (see above).
/// 2. Nested loop over every `(literal from c1, literal from c2)` pair.
///    Skip immediately (no unification attempted) if polarities match or
///    predicates differ — this is a cheap O(1) filter before paying for the
///    O(arity) unification attempt.
/// 3. For each surviving candidate pair: unify with a BRAND NEW
///    `Substitution` (never reused across pairs — a failed attempt must not
///    leak partial bindings into the next candidate pair's attempt).
/// 4. On success: build the resolvent = every literal from `c1` EXCEPT the
///    matched one, plus every literal from `c2` EXCEPT the matched one, all
///    with the winning substitution applied.
///
/// **Complexity:** O(|c1| × |c2|) candidate pairs considered, each costing up
/// to O(unification cost) — this is the brute-force approach flagged for a
/// discrimination-tree-based replacement in v0.3 (see TODO below).
pub fn resolve(
    c1: &Clause,
    c2: &Clause,
    var_gen: &mut VarGen,
    arena: &mut TermArena
) -> Vec<InferenceResult> {
    let lits1 = rename_apart(&c1.literals, var_gen, arena);
    let lits2 = rename_apart(&c2.literals, var_gen, arena);

    let mut results = Vec::new();

    for (i, l1) in lits1.iter().enumerate() {
        for (j, l2) in lits2.iter().enumerate() {
            if l1.polarity == l2.polarity || l1.predicate != l2.predicate {
                continue;
            }

            // Fresh substitution per candidate pair — a failure here must
            // not contaminate the next pair's attempt.
            let mut subst = Substitution::new();
            if !unify_literals(l1, l2, arena, &mut subst) {
                continue;
            }

            let mut new_literals = Vec::with_capacity(lits1.len() - 1 + lits2.len() - 1);
            for (k, lit) in lits1.iter().enumerate() {
                if k != i {
                    new_literals.push(apply_to_literal(lit, &subst, arena));
                }
            }
            for (k, lit) in lits2.iter().enumerate() {
                if k != j {
                    new_literals.push(apply_to_literal(lit, &subst, arena));
                }
            }

            results.push((
                new_literals,
                InferenceInfo::from_rule(InferenceRule::Resolution, vec![c1.id, c2.id]),
            ));
        }
    }

    results
}

// TODO(v0.3 — perf, the big one): `resolve`'s O(|c1| × |c2|) nested loop,
// repeated for EVERY pair of clauses considered by the given-clause loop, is
// the textbook case for discrimination-tree indexing. Instead of checking
// every literal in `active` against the given clause one by one, a real
// prover indexes active clauses' literals by predicate+argument shape so it
// can directly query "which literals could possibly unify with this one" in
// closer to O(log n) or O(matches found) instead of O(all active literals).
// This is THE main reason v0.1 will not scale past small problems — don't
// bother micro-optimizing anything else in this file before this lands.

/// Try Factoring: find every pair of literals WITHIN `c` itself (same
/// polarity, same predicate) that can be unified, merging them into one
/// literal (drop one of the pair, keep the other with the unifying
/// substitution applied across the whole clause). Returns ALL possible
/// factoring results.
///
/// No rename-apart needed: literals within one clause already share the
/// same variable scope by construction.
///
/// **Algorithm:** same shape as `resolve`'s inner loop, but over pairs
/// `(i, j)` with `i < j` WITHIN a single clause's literal list, requiring
/// SAME polarity and SAME predicate (the opposite filter condition from
/// Resolution — this is intentional, factoring merges duplicates, it
/// doesn't resolve contradictions). On a successful unification, the
/// resulting clause keeps literal `i` (substituted) and drops literal `j`
/// entirely; every OTHER literal in the clause also gets the substitution
/// applied (since the unification may have bound variables that appear
/// elsewhere in the clause too).
///
/// **Complexity:** O(|c|²) candidate pairs within the clause, each up to
/// O(unification cost). Clauses are typically small (a handful of literals),
/// so this quadratic factor rarely matters in practice — unlike `resolve`'s
/// version of the same problem, which scales with the size of the ENTIRE
/// active set.
pub fn factor(c: &Clause, arena: &mut TermArena) -> Vec<InferenceResult> {
    let lits = &c.literals;
    let mut results = Vec::new();

    for i in 0..lits.len() {
        for j in i + 1..lits.len() {
            if lits[i].polarity != lits[j].polarity || lits[i].predicate != lits[j].predicate {
                continue;
            }

            let mut subst = Substitution::new();
            if !unify_literals(&lits[i], &lits[j], arena, &mut subst) {
                continue;
            }

            let mut new_literals = Vec::with_capacity(lits.len() - 1);
            for (k, lit) in lits.iter().enumerate() {
                if k == j {
                    continue; // drop the duplicate; k == i is kept below (with subst applied)
                }
                new_literals.push(apply_to_literal(lit, &subst, arena));
            }

            results.push((
                new_literals,
                InferenceInfo::from_rule(InferenceRule::Factoring, vec![c.id]),
            ));
        }
    }

    results
}

// TODO(v0.2 — equality reasoning): this file will gain three new inference
// functions with a similar shape to `resolve`/`factor`:
//   - `superposition_left` / `superposition_right` — rewrite one clause's
//     literal using an equation from another clause, restricted by the KBO
//     term ordering (which doesn't exist yet — see term.rs/a future
//     ordering.rs) to keep the rule terminating.
//   - `equality_resolution` — resolve away a literal of the form `~ (s = s)`
//     directly (unifies s with itself, no second clause needed).
//   - `equality_factoring` — the equality analogue of `factor` above.
// All three will need the "one-directional matching" operation flagged as a
// TODO in unify.rs (`match_term`), not plain bidirectional `unify`. Expect
// this file to roughly double in size when that lands; consider splitting
// `resolution.rs` / `factoring.rs` / `superposition.rs` into separate files
// under an `inference/` directory at that point rather than one flat module.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{ SymbolTable, TermArena, TermData };
    use crate::clause::{ ClauseStore, InferenceInfo, InferenceRule, Literal };
    struct Fixture {
        symbols: SymbolTable,
        p: u32, // predicate P/1
        q: u32, // predicate Q/1
        r: u32, // predicate R/1
        a: u32, // constant a
        b: u32, // constant b
        c: u32, // constant c
    }

    fn fixture() -> Fixture {
        let mut symbols = SymbolTable::new();
        let p = symbols.intern("P");
        let q = symbols.intern("Q");
        let r = symbols.intern("R");
        let a = symbols.intern("a");
        let b = symbols.intern("b");
        let c = symbols.intern("c");
        Fixture { symbols, p, q, r, a, b, c }
    }

    /// Collect all raw `VarId`s used in a set of literals (to verify disjointness
    /// between rename results).
    fn vars_used(literals: &[Literal], arena: &TermArena) -> HashSet<u32> {
        fn walk(t: u32, arena: &TermArena, out: &mut HashSet<u32>) {
            match arena.get(t) {
                TermData::Var(v) => {
                    out.insert(v);
                }
                TermData::App(..) => {
                    for &a in arena.args(t) {
                        walk(a, arena, out);
                    }
                }
            }
        }
        let mut out = HashSet::new();
        for lit in literals {
            for &t in &lit.args {
                walk(t, arena, &mut out);
            }
        }
        out
    }

    #[test]
    fn rename_apart_is_identity_for_ground_clause() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let literals = vec![Literal::positive(fx.p, vec![a])];
        let mut var_gen = VarGen::new();

        let renamed = rename_apart(&literals, &mut var_gen, &mut arena);
        assert_eq!(renamed, literals, "a clause without variables must remain unchanged");
    }

    #[test]
    fn rename_apart_keeps_repeated_variable_consistent() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        // P(X) | Q(X) -- X appears twice, must map to the SAME fresh var.
        let literals = vec![Literal::positive(fx.p, vec![x]), Literal::positive(fx.q, vec![x])];
        let mut var_gen = VarGen::new();

        let renamed = rename_apart(&literals, &mut var_gen, &mut arena);
        assert_eq!(
            renamed[0].args[0],
            renamed[1].args[0],
            "X in both literals must remain identical after rename"
        );
        // But its id must differ from the original variable (original var id 0, if var_gen also starts from 0
        // it could coincidentally collide in value -- what matters is checking *consistency*, covered above).
    }

    #[test]
    fn rename_apart_produces_disjoint_variables_across_two_calls() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0); // clause 1 uses var 0
        let y = arena.mk_var(0); // clause 2 ALSO uses var 0 (different scope, coincidentally the same)
        assert_eq!(x, y, "intentional: two independent clauses can have the same raw var id");

        let lits1 = vec![Literal::positive(fx.p, vec![x])];
        let lits2 = vec![Literal::positive(fx.q, vec![y])];

        let mut var_gen = VarGen::new();
        let renamed1 = rename_apart(&lits1, &mut var_gen, &mut arena);
        let renamed2 = rename_apart(&lits2, &mut var_gen, &mut arena);

        let vars1 = vars_used(&renamed1, &arena);
        let vars2 = vars_used(&renamed2, &arena);

        assert!(
            vars1.is_disjoint(&vars2),
            "renamed variables from two different clauses must not overlap: {vars1:?} vs {vars2:?}"
        );
    }

    #[test]
    fn resolve_produces_empty_clause_from_direct_contradiction() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let x = arena.mk_var(0);
        let a = arena.mk_app(fx.a, &[]);

        // C1: P(X)   C2: ~P(a)
        let c1 = store.insert(
            vec![Literal::positive(fx.p, vec![x])],
            InferenceInfo::input(),
            &arena
        );
        let c2 = store.insert(
            vec![Literal::negative(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );

        let mut var_gen = VarGen::new();
        let results = resolve(store.get(c1), store.get(c2), &mut var_gen, &mut arena);

        assert_eq!(results.len(), 1);
        let (literals, info) = &results[0];
        assert!(literals.is_empty(), "P(X) resolution with ~P(a) must produce an empty clause");
        assert_eq!(info.rule, InferenceRule::Resolution);
        assert_eq!(info.parents, vec![c1, c2]);
    }

    #[test]
    fn resolve_keeps_remaining_literals_with_substitution_applied() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let x = arena.mk_var(0);
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // C1: P(X) | Q(X)      C2: ~P(a) | R(b)
        // Resolution on the complement pair P(X)/~P(a) (X=a) -> remaining: Q(a) | R(b)
        let c1 = store.insert(
            vec![Literal::positive(fx.p, vec![x]), Literal::positive(fx.q, vec![x])],
            InferenceInfo::input(),
            &arena
        );
        let c2 = store.insert(
            vec![Literal::negative(fx.p, vec![a]), Literal::positive(fx.r, vec![b])],
            InferenceInfo::input(),
            &arena
        );

        let mut var_gen = VarGen::new();
        let results = resolve(store.get(c1), store.get(c2), &mut var_gen, &mut arena);

        assert_eq!(results.len(), 1, "there is only one complementary literal pair (P/~P)");
        let (literals, _) = &results[0];
        assert_eq!(literals.len(), 2);

        // The resolvent should be fully ground: Q(a) and R(b).
        let mut symbols_used: Vec<String> = literals
            .iter()
            .map(|l| l.display(&arena, &fx.symbols))
            .collect();
        symbols_used.sort();
        assert_eq!(symbols_used, vec!["Q(a)".to_string(), "R(b)".to_string()]);
    }

    #[test]
    fn resolve_finds_all_complementary_pairs() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);
        let c = arena.mk_app(fx.c, &[]);

        // C1: P(a) | Q(c)      C2: ~P(a) | ~Q(c)
        // Two independent complementary pairs -> must produce 2 resolvents.
        let c1 = store.insert(
            vec![Literal::positive(fx.p, vec![a]), Literal::positive(fx.q, vec![c])],
            InferenceInfo::input(),
            &arena
        );
        let c2 = store.insert(
            vec![Literal::negative(fx.p, vec![a]), Literal::negative(fx.q, vec![c])],
            InferenceInfo::input(),
            &arena
        );

        let mut var_gen = VarGen::new();
        let results = resolve(store.get(c1), store.get(c2), &mut var_gen, &mut arena);

        assert_eq!(
            results.len(),
            2,
            "there must be 2 resolvents: from pair P/~P and from pair Q/~Q"
        );
        for (literals, _) in &results {
            assert_eq!(
                literals.len(),
                2,
                "each resolvent leaves 2 literals (one from each clause)"
            );
        }
    }

    #[test]
    fn resolve_returns_empty_when_no_complementary_literals() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // C1: P(a)   C2: Q(b) -- completely different predicates, none are complementary.
        let c1 = store.insert(
            vec![Literal::positive(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );
        let c2 = store.insert(
            vec![Literal::positive(fx.q, vec![b])],
            InferenceInfo::input(),
            &arena
        );

        let mut var_gen = VarGen::new();
        let results = resolve(store.get(c1), store.get(c2), &mut var_gen, &mut arena);

        assert!(results.is_empty());
    }

    #[test]
    fn resolve_fails_pair_when_unification_fails_but_tries_others() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // C1: P(a) | Q(a)     C2: ~P(b) | ~Q(a)
        // Pair P(a)/~P(b): predicates match but args (a vs b) fail to unify -> no resolvent produced.
// Pair Q(a)/~Q(a): succeeds -> produces a resolvent.
        let c1 = store.insert(
            vec![Literal::positive(fx.p, vec![a]), Literal::positive(fx.q, vec![a])],
            InferenceInfo::input(),
            &arena
        );
        let c2 = store.insert(
            vec![Literal::negative(fx.p, vec![b]), Literal::negative(fx.q, vec![a])],
            InferenceInfo::input(),
            &arena
        );

        let mut var_gen = VarGen::new();
        let results = resolve(store.get(c1), store.get(c2), &mut var_gen, &mut arena);

        assert_eq!(results.len(), 1, "only pair Q(a)/~Q(a) succeeds in unifying");
        let (literals, _) = &results[0];
        let mut rendered: Vec<String> = literals
            .iter()
            .map(|l| l.display(&arena, &fx.symbols))
            .collect();
        rendered.sort();
        assert_eq!(rendered, vec!["P(a)".to_string(), "~P(b)".to_string()]);
    }

    // ---------- factor ----------

    #[test]
    fn factor_merges_identical_ground_duplicate_literal() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);

        // C: P(a) | P(a)  -- exact duplicate literals
        let c = store.insert(
            vec![Literal::positive(fx.p, vec![a]), Literal::positive(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );

        let results = factor(store.get(c), &mut arena);
        assert_eq!(results.len(), 1);
        let (literals, info) = &results[0];
        assert_eq!(literals.len(), 1, "two identical P(a) literals must be merged into one single literal");
        assert_eq!(literals[0].display(&arena, &fx.symbols), "P(a)");
        assert_eq!(info.rule, InferenceRule::Factoring);
        assert_eq!(info.parents, vec![c]);
    }

    #[test]
    fn factor_unifies_variable_with_constant_across_two_literals() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let x = arena.mk_var(0);
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // C: P(X) | P(a) | Q(b)
        // P(X) & P(a) can be unified (X=a) -> result: P(a) | Q(b)
        let c = store.insert(
            vec![
                Literal::positive(fx.p, vec![x]),
                Literal::positive(fx.p, vec![a]),
                Literal::positive(fx.q, vec![b])
            ],
            InferenceInfo::input(),
            &arena
        );

        let results = factor(store.get(c), &mut arena);
        assert_eq!(results.len(), 1);
        let (literals, _) = &results[0];
        assert_eq!(literals.len(), 2);

        let mut rendered: Vec<String> = literals
            .iter()
            .map(|l| l.display(&arena, &fx.symbols))
            .collect();
        rendered.sort();
        assert_eq!(rendered, vec!["P(a)".to_string(), "Q(b)".to_string()]);
    }

    #[test]
    fn factor_returns_empty_when_no_mergeable_literals() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // C: P(a) | Q(b) -- different predicates, nothing can be merged.
        let c = store.insert(
            vec![Literal::positive(fx.p, vec![a]), Literal::positive(fx.q, vec![b])],
            InferenceInfo::input(),
            &arena
        );

        let results = factor(store.get(c), &mut arena);
        assert!(results.is_empty());
    }

    #[test]
    fn factor_ignores_pair_with_different_polarity() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);

        // C: P(a) | ~P(a) -- same predicate & args but different polarity, NOT a factoring candidate.
        let c = store.insert(
            vec![Literal::positive(fx.p, vec![a]), Literal::negative(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );

        let results = factor(store.get(c), &mut arena);
        assert!(
            results.is_empty(),
            "different polarities must not be factored (that is the job of Resolution, not Factoring)"
        );
    }
}
