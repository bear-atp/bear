//! `Literal` and `Clause` representation.
//!
//! A clause is a disjunction of literals, represented as `Vec<Literal>`
//! (`[]` = the empty clause = `⊥` = a found contradiction/proof). Every
//! `Clause` carries `InferenceInfo` (which rule produced it + its parent
//! clause ids) from the moment it's created — this is NOT optional or
//! bolted on later, specifically so proof reconstruction never needs a
//! retrofit (see README §3.2).
//!
//! Computing a clause's `weight` needs access to `TermArena` (weight = total
//! symbol count across all terms in its literals), so `Clause` itself never
//! computes its own weight — that's `ClauseStore::insert`'s job, which is
//! also the ONLY way a `Clause` gets created (see the note on `ClauseStore`
//! below for why that matters).

use crate::term::{ SymbolId, TermArena, TermId };

/// One literal: `predicate(args...)`, or its negation `~predicate(args...)`.
///
/// **Why `#[derive(PartialEq, Eq, Hash)]` is safe here without a custom
/// impl:** because `TermArena` already does hash-consing (see `term.rs`),
/// two structurally-identical terms always share the same `TermId`. So
/// comparing `args: Vec<TermId>` field-by-field with plain `==` is already
/// a correct STRUCTURAL comparison for ground literals — we don't need to
/// walk into the term tree ourselves. (For literals containing variables,
/// `==` still only means "identical up to variable naming", NOT "unifiable"
/// — that distinction matters, see `is_complementary_ground` below.)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    pub polarity: bool, // true = positive, false = negative
    pub predicate: SymbolId,
    pub args: Vec<TermId>,
}

impl Literal {
    pub fn positive(predicate: SymbolId, args: Vec<TermId>) -> Self {
        Self { polarity: true, predicate, args }
    }

    pub fn negative(predicate: SymbolId, args: Vec<TermId>) -> Self {
        Self { polarity: false, predicate, args }
    }

    pub fn is_positive(&self) -> bool {
        self.polarity
    }

    pub fn is_negative(&self) -> bool {
        !self.polarity
    }

    /// Return a NEW literal with polarity flipped. Does not mutate `self`.
    ///
    /// **Complexity:** O(arity) — clones `args`.
    pub fn negate(&self) -> Literal {
        Literal { polarity: !self.polarity, predicate: self.predicate, args: self.args.clone() }
    }

    pub fn arity(&self) -> usize {
        self.args.len()
    }

    /// Check whether two GROUND literals (no variables) are exact
    /// complements: same predicate, same args (positionally, term-for-term),
    /// opposite polarity.
    ///
    /// **Algorithm:** three flat equality checks — polarity differs,
    /// predicate matches, and `args` (a `Vec<TermId>`) matches element-wise.
    /// Thanks to hash-consing in `TermArena`, `args == other.args` is a
    /// correct structural check without needing to dereference into the
    /// arena at all — this function doesn't even take a `&TermArena`
    /// parameter, which is a direct consequence of interning.
    ///
    /// **Complexity:** O(arity).
    ///
    /// **What this is NOT:** this is not the general check used by
    /// `Resolution`. Two literals like `P(X)` and `P(a)` are NOT considered
    /// complementary by this function even though they're unifiable (X could
    /// bind to a) — it only catches EXACT term matches. Real resolution uses
    /// `unify::unify_literals` instead (see `unify.rs`), which handles
    /// variables properly. This function exists as a quick sanity check /
    /// for genuinely ground clauses where full unification would be
    /// overkill.
    pub fn is_complementary_ground(&self, other: &Literal) -> bool {
        self.polarity != other.polarity &&
            self.predicate == other.predicate &&
            self.args == other.args
    }

    /// Literal weight: 1 (for the predicate symbol itself) + the summed
    /// `TermArena::size()` of every argument. Used by `ClauseStore` to
    /// compute `Clause::weight`.
    ///
    /// **Complexity:** O(total size of all argument terms) — each `size()`
    /// call is itself a full tree walk (see `term.rs`), so this is NOT O(1)
    /// despite looking like a simple sum.
    pub fn weight(&self, arena: &TermArena) -> u32 {
        1 +
            self.args
                .iter()
                .map(|&t| arena.size(t))
                .sum::<u32>()
    }

    /// Render as `pred(a, b)` or `~pred(a, b)`. Debug/test use only, not a
    /// real proof-output format.
    ///
    /// **Complexity:** O(total size of argument terms) — delegates to
    /// `TermArena::display` per argument, same allocation caveats apply
    /// (see `// TODO(v0.3)` in `term.rs`'s `display`).
    pub fn display(&self, arena: &TermArena, symbols: &crate::term::SymbolTable) -> String {
        let name = symbols.name(self.predicate);
        let sign = if self.polarity { "" } else { "~" };
        if self.args.is_empty() {
            format!("{sign}{name}")
        } else {
            let args_str: Vec<String> = self.args
                .iter()
                .map(|&t| arena.display(t, symbols))
                .collect();
            format!("{sign}{name}({})", args_str.join(", "))
        }
    }
}

// TODO(v0.2 — equality reasoning): once `=` becomes a "real" predicate for
// Superposition purposes, decide whether it needs special-casing here (e.g.
// a dedicated `is_equality()` check, since `=` literals get treated
// differently by Superposition/Demodulation than ordinary predicates — they
// can be used to REWRITE other literals, not just resolved against). Likely
// lands as a new method on `Literal` plus a reserved `SymbolId` convention,
// TBD once the KBO ordering work clarifies what's actually needed.

/// Unique id for a clause within one `ClauseStore`.
pub type ClauseId = u32;

/// Which inference rule produced a clause.
///
/// `Superposition`, `EqualityResolution`, `EqualityFactoring`, `Demodulation`
/// are not used until v0.2 (equality reasoning lands), but are listed here
/// from day one so `InferenceInfo`/the proof format never needs a breaking
/// change later — adding a new rule variant is additive, not a migration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceRule {
    /// Clause came directly from the input problem (an axiom or the negated
    /// goal), not derived by any inference rule.
    Input,
    Resolution,
    Factoring,
    Superposition, // TODO(v0.2): not yet implemented, see inference.rs
    EqualityResolution, // TODO(v0.2): not yet implemented
    EqualityFactoring, // TODO(v0.2): not yet implemented
    Demodulation, // TODO(v0.2): not yet implemented
}

/// Provenance metadata for one clause: which rule produced it, and which
/// clauses were its premises. Mandatory on every `Clause` so a proof can be
/// reconstructed by walking backward from the empty clause to the `Input`
/// clauses at the roots.
#[derive(Debug, Clone)]
pub struct InferenceInfo {
    pub rule: InferenceRule,
    pub parents: Vec<ClauseId>,
}

impl InferenceInfo {
    pub fn input() -> Self {
        Self { rule: InferenceRule::Input, parents: Vec::new() }
    }

    pub fn from_rule(rule: InferenceRule, parents: Vec<ClauseId>) -> Self {
        Self { rule, parents }
    }
}

/// A clause: a disjunction of literals, plus given-clause-loop bookkeeping
/// (`age`, `weight`) and proof-reconstruction metadata (`inference`).
#[derive(Debug, Clone)]
pub struct Clause {
    pub id: ClauseId,
    pub literals: Vec<Literal>,
    /// Birth order (0 = the very first input clause). Currently UNUSED by
    /// the v0.1 given-clause loop (which is plain FIFO — see
    /// `saturation.rs`), but already tracked because the v0.2 age-weight
    /// ratio queue needs it and retrofitting age tracking onto existing
    /// clauses later would be much messier than just always recording it.
    pub age: u32,
    /// Total symbol-count weight across all literals. Same story as `age`:
    /// tracked now, not yet consumed by the (currently FIFO) queue.
    pub weight: u32,
    pub inference: InferenceInfo,
}

impl Clause {
    /// The empty clause (`⊥`) signals a contradiction was found — proof done.
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn num_literals(&self) -> usize {
        self.literals.len()
    }

    /// Render as `lit1 | lit2 | ...`, or `⊥` for the empty clause.
    pub fn display(&self, arena: &TermArena, symbols: &crate::term::SymbolTable) -> String {
        if self.literals.is_empty() {
            return "⊥".to_string();
        }
        self.literals
            .iter()
            .map(|l| l.display(arena, symbols))
            .collect::<Vec<_>>()
            .join(" | ")
    }
}

/// Owns every clause alive during one proof search, and is the ONLY thing
/// allowed to allocate a `ClauseId` or compute a `weight`.
///
/// `Clause`'s constructor is deliberately not exposed publicly — every
/// clause MUST go through `ClauseStore::insert` so that `id`, `age`, and
/// `weight` stay internally consistent (no two clauses ever get the same
/// `id`; `weight` is never forgotten/stale). This is the same "smart
/// constructor" pattern you'd reach for in any language, just enforced here
/// via Rust's module privacy instead of a runtime check.
#[derive(Debug, Default)]
pub struct ClauseStore {
    clauses: Vec<Clause>,
    next_age: u32,
}

impl ClauseStore {
    pub fn new() -> Self {
        Self { clauses: Vec::new(), next_age: 0 }
    }

    /// Insert a new clause. `id` and `age` are assigned in insertion order
    /// (they're literally the same counter, `id == age` always holds today
    /// — that's an implementation coincidence, not a guaranteed invariant,
    /// don't rely on it), and `weight` is computed from `arena`.
    ///
    /// **Algorithm:** grab the next sequential id/age, sum up
    /// `Literal::weight()` across all literals (O(clause size) — see the
    /// note on `Literal::weight` above about this NOT being O(literal
    /// count)), push the fully-built `Clause`.
    ///
    /// **Complexity:** O(total term size across all literals in the clause).
    pub fn insert(
        &mut self,
        literals: Vec<Literal>,
        inference: InferenceInfo,
        arena: &TermArena
    ) -> ClauseId {
        let id = self.clauses.len() as u32;
        let age = self.next_age;
        self.next_age += 1;
        let weight = literals
            .iter()
            .map(|l| l.weight(arena))
            .sum();

        self.clauses.push(Clause { id, literals, age, weight, inference });
        id
    }

    /// **Complexity:** O(1), direct index.
    ///
    /// # Panics
    /// Panics if `id` was never returned by `insert` on THIS store (same
    /// caveat as `TermArena::get`/`SymbolTable::name` — no cross-store
    /// validity tag).
    pub fn get(&self, id: ClauseId) -> &Clause {
        &self.clauses[id as usize]
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Iterate every stored clause in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter()
    }

    /// Walk a proof backward from `from` (typically the empty clause) all
    /// the way to its root `Input` clauses, returning the clauses involved
    /// in TOPOLOGICAL order (every parent appears before its child, `from`
    /// itself appears last).
    ///
    /// **Algorithm:** classic DFS-based topological sort / post-order
    /// traversal over the "derived-from" DAG (clauses as nodes, `parents`
    /// as edges pointing backward in time). `visited` prevents re-walking
    /// (and re-emitting) a clause that's a shared ancestor of multiple
    /// branches — this can genuinely happen, e.g. the same axiom used twice
    /// in one proof. Recursion happens FIRST (walk into parents), then the
    /// current clause is pushed onto `order` AFTER — that post-order push
    /// is exactly what guarantees "parents before children" in the final
    /// list.
    ///
    /// **Complexity:** O(V + E) where V = number of distinct clauses reachable
    /// backward from `from`, E = total number of parent-edges among them.
    /// Each clause is visited at most once thanks to the `visited` set.
    pub fn proof_trace(&self, from: ClauseId) -> Vec<ClauseId> {
        let mut visited = std::collections::HashSet::new();
        let mut order = Vec::new();
        self.proof_trace_rec(from, &mut visited, &mut order);
        order
    }

    fn proof_trace_rec(
        &self,
        id: ClauseId,
        visited: &mut std::collections::HashSet<ClauseId>,
        order: &mut Vec<ClauseId>
    ) {
        if !visited.insert(id) {
            return; // already emitted this clause via another branch, skip
        }
        let clause = self.get(id);
        for &parent in &clause.inference.parents {
            self.proof_trace_rec(parent, visited, order);
        }
        order.push(id); // post-order: push AFTER recursing into parents
    }
}

// TODO(v0.2 — simplification): once subsumption / tautology deletion /
// forward-backward simplification land, `ClauseStore` will likely need a way
// to mark a clause as "deleted"/"redundant" without actually removing it
// (removing would invalidate every other clause's `ClauseId` indices, since
// `get()` does direct indexing). Probably a `deleted: Vec<bool>` parallel
// array, or wrapping `clauses` in `Vec<Option<Clause>>` — decide once
// subsumption's actual access pattern is clearer, don't guess now.
 
// TODO(v0.4 — ML clause selection): `ClauseFeatures` extraction (README §4.2)
// will want to read off of `Clause`/`Literal` (weight, age, arity, symbol
// histogram, depth) largely as-is — most of the raw numbers it needs already
// exist on this struct. The main missing piece will be "goal similarity",
// which needs the saturation loop to know which clause(s) are the negated
// goal — not tracked anywhere right now (all `Input` clauses look the same
// to `ClauseStore`). Worth tagging goal clauses specially before v0.4 starts.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::SymbolTable;

    /// Fixture only contains `SymbolTable` (shared across tests within a function
    /// if needed). `TermArena` is intentionally created per test so that each
    /// test is independent of one another.
    ///

    struct Fixture {
        symbols: SymbolTable,
        p: u32, // predicate P/1
        q: u32, // predicate Q/2
        f: u32, // function f/1
        a: u32, // constant a
        b: u32, // constant b
    }

    fn fixture() -> Fixture {
        let mut symbols = SymbolTable::new();
        let p = symbols.intern("P");
        let q = symbols.intern("Q");
        let f = symbols.intern("f");
        let a = symbols.intern("a");
        let b = symbols.intern("b");
        Fixture { symbols, p, q, f, a, b }
    }

    #[test]
    fn literal_polarity_and_negate() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a_term = arena.mk_app(fx.a, &[]);

        let pos = Literal::positive(fx.p, vec![a_term]);
        assert!(pos.is_positive());
        assert!(!pos.is_negative());

        let neg = pos.negate();
        assert!(neg.is_negative());
        assert_eq!(neg.predicate, pos.predicate);
        assert_eq!(neg.args, pos.args);

        // negate() does not mutate the original literal
        assert!(pos.is_positive());
    }

    #[test]
    fn literal_arity() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        let unary = Literal::positive(fx.p, vec![a]);
        let binary = Literal::positive(fx.q, vec![a, b]);

        assert_eq!(unary.arity(), 1);
        assert_eq!(binary.arity(), 2);
    }

    #[test]
    fn ground_complementary_literals() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        let p_a_pos = Literal::positive(fx.p, vec![a]);
        let p_a_neg = Literal::negative(fx.p, vec![a]);
        let p_b_neg = Literal::negative(fx.p, vec![b]);
        let q_a_neg = Literal::negative(fx.q, vec![a, a]);

        assert!(p_a_pos.is_complementary_ground(&p_a_neg));
        assert!(p_a_neg.is_complementary_ground(&p_a_pos)); // symmetric

        // Different arguments -> not complements even if predicate & polarity match.
        assert!(!p_a_pos.is_complementary_ground(&p_b_neg));

        // Different predicate -> not complements.
        assert!(!p_a_pos.is_complementary_ground(&q_a_neg));

        // Same polarity -> not complements.
        assert!(!p_a_pos.is_complementary_ground(&Literal::positive(fx.p, vec![a])));
    }

    #[test]
    fn literal_weight_counts_predicate_and_arg_sizes() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]); // size 1
        let fa = arena.mk_app(fx.f, &[a]); // size 2

        // P(a): 1 (predicate) + size(a)=1 => 2
        let lit_a = Literal::positive(fx.p, vec![a]);
        assert_eq!(lit_a.weight(&arena), 2);

        // P(f(a)): 1 (predicate) + size(f(a))=2 => 3
        let lit_fa = Literal::positive(fx.p, vec![fa]);
        assert_eq!(lit_fa.weight(&arena), 3);

        // Propositional (arity 0): predicate only => 1
        let prop = Literal::positive(fx.p, vec![]);
        assert_eq!(prop.weight(&arena), 1);
    }

    #[test]
    fn clause_store_assigns_sequential_id_and_age() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);

        let c0 = store.insert(
            vec![Literal::positive(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );
        let c1 = store.insert(
            vec![Literal::negative(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );

        assert_eq!(c0, 0);
        assert_eq!(c1, 1);
        assert_eq!(store.get(c0).age, 0);
        assert_eq!(store.get(c1).age, 1);
        assert_eq!(store.len(), 2);
    }

    #[test]
    fn clause_weight_is_sum_of_literal_weights() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // P(a) | ~Q(a, b) => weight = (1+1) + (1+1+1) = 2 + 3 = 5
        let literals = vec![Literal::positive(fx.p, vec![a]), Literal::negative(fx.q, vec![a, b])];
        let id = store.insert(literals, InferenceInfo::input(), &arena);
        assert_eq!(store.get(id).weight, 5);
    }

    #[test]
    fn empty_clause_detected() {
        let arena = TermArena::new();
        let mut store = ClauseStore::new();
        let id = store.insert(vec![], InferenceInfo::input(), &arena);

        assert!(store.get(id).is_empty());
        assert_eq!(store.get(id).weight, 0);
    }

    #[test]
    fn non_empty_clause_is_not_empty() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);
        let id = store.insert(
            vec![Literal::positive(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );

        assert!(!store.get(id).is_empty());
    }

    #[test]
    fn inference_info_tracks_rule_and_parents() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);

        let parent1 = store.insert(
            vec![Literal::positive(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );
        let parent2 = store.insert(
            vec![Literal::negative(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );
        let resolvent = store.insert(
            vec![], // resolution of P(a) with ~P(a) -> empty clause
            InferenceInfo::from_rule(InferenceRule::Resolution, vec![parent1, parent2]),
            &arena
        );

        let inf = &store.get(resolvent).inference;
        assert_eq!(inf.rule, InferenceRule::Resolution);
        assert_eq!(inf.parents, vec![parent1, parent2]);
        assert_eq!(store.get(parent1).inference.rule, InferenceRule::Input);
    }

    #[test]
    fn proof_trace_walks_back_to_input_clauses() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);

        // c0, c1 = input; c2 = resolvent(c0, c1); c3 = factoring(c2) (dummy, to make a 2-level chain)
        let c0 = store.insert(
            vec![Literal::positive(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );
        let c1 = store.insert(
            vec![Literal::negative(fx.p, vec![a])],
            InferenceInfo::input(),
            &arena
        );
        let c2 = store.insert(
            vec![],
            InferenceInfo::from_rule(InferenceRule::Resolution, vec![c0, c1]),
            &arena
        );
        let c3 = store.insert(
            vec![],
            InferenceInfo::from_rule(InferenceRule::Factoring, vec![c2]),
            &arena
        );

        let trace = store.proof_trace(c3);

        // Parents must appear before children in the trace (topological order).
        let pos = |id: u32|
            trace
                .iter()
                .position(|&x| x == id)
                .unwrap();
        assert!(pos(c0) < pos(c2));
        assert!(pos(c1) < pos(c2));
        assert!(pos(c2) < pos(c3));
        assert_eq!(*trace.last().unwrap(), c3);
        assert_eq!(trace.len(), 4);
    }

    #[test]
    fn clause_display_formats_literals_with_bar_separator() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let mut store = ClauseStore::new();
        let a = arena.mk_app(fx.a, &[]);

        let id = store.insert(
            vec![Literal::positive(fx.p, vec![a]), Literal::negative(fx.q, vec![a, a])],
            InferenceInfo::input(),
            &arena
        );

        let text = store.get(id).display(&arena, &fx.symbols);
        assert_eq!(text, "P(a) | ~Q(a, a)");
    }

    #[test]
    fn empty_clause_displays_as_bottom_symbol() {
        let arena = TermArena::new();
        let symbols = SymbolTable::new();
        let mut store = ClauseStore::new();
        let id = store.insert(vec![], InferenceInfo::input(), &arena);

        assert_eq!(store.get(id).display(&arena, &symbols), "⊥");
    }
}
