//! The given-clause loop (saturation) — v0.1 version: **naive FIFO**, no
//! age-weight priority yet (that's v0.2, README §2), no indexing (v0.3), and
//! no simplification/subsumption (v0.2).
//!
//! The overall shape is the textbook saturation-based prover loop:
//! 1. All input clauses go into the `passive` queue.
//! 2. Pop the front clause off `passive` (the "given clause").
//! 3. If the given clause is empty (`⊥`) → proof found, stop.
//! 4. Try `Factoring` on the given clause against itself.
//! 5. Try `Resolution` between the given clause and EVERY clause in `active`.
//! 6. Every new clause from steps 4 & 5 goes into `passive`.
//! 7. The given clause moves into `active`.
//! 8. Repeat from step 2. If `passive` ever empties out without hitting an
//!    empty clause → the clause set is "saturated" (no contradiction
//!    derivable with the rules currently available).

use std::collections::VecDeque;

use crate::clause::{ Clause, ClauseId, ClauseStore, InferenceInfo, Literal };
use crate::inference::{ factor, resolve, VarGen };
use crate::term::TermArena;

/// The final outcome of one saturation session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SaturationResult {
    /// An empty clause was derived — contradiction found, proof complete.
    /// The `ClauseId` points at that empty clause; walk
    /// `Saturation::proof_trace` from it to see the full derivation.
    Proved(ClauseId),
    /// `passive` ran out without ever deriving an empty clause. For v0.1
    /// (Resolution + Factoring only, no equality), this means the clause
    /// set is consistent as far as the currently available rules can prove.
    /// NOTE: this is NOT a claim of satisfiability in general — a problem
    /// that genuinely needs equality reasoning (not available until v0.2)
    /// would ALSO report `Saturated` here even if it's actually
    /// unsatisfiable, simply because the rules needed to prove it don't
    /// exist yet. Don't over-interpret `Saturated` as "verified consistent".
    Saturated,
    /// Stopped because `ClauseStore`'s total clause count hit `max_clauses`
    /// (passed into `run`) before either of the above outcomes happened.
    /// This is a simple stand-in for "Timeout" in v0.1 — clause-count-based
    /// rather than wall-clock-based. A real time-based cutoff can be added
    /// later without changing this API's shape (see TODO below).
    ClauseLimitReached,
}

/// Full state of one proof-search session: the term arena, clause store,
/// variable generator (for rename-apart), and the two clause sets
/// (`active` / `passive`) that define the given-clause algorithm.
pub struct Saturation {
    arena: TermArena,
    clause_store: ClauseStore,
    var_gen: VarGen,
    active: Vec<ClauseId>,
    passive: VecDeque<ClauseId>,
}

impl Saturation {
    pub fn new() -> Self {
        Self {
            arena: TermArena::new(),
            clause_store: ClauseStore::new(),
            var_gen: VarGen::new(),
            active: Vec::new(),
            passive: VecDeque::new(),
        }
    }

    /// Access the `TermArena` to build terms BEFORE calling
    /// `add_input_clause` (predicate/constant/variable terms must already
    /// exist in THIS arena, not some other one, for their `TermId`s to be
    /// valid here).
    pub fn arena_mut(&mut self) -> &mut TermArena {
        &mut self.arena
    }

    pub fn arena(&self) -> &TermArena {
        &self.arena
    }

    pub fn clause_store(&self) -> &ClauseStore {
        &self.clause_store
    }

    pub fn active_len(&self) -> usize {
        self.active.len()
    }

    pub fn passive_len(&self) -> usize {
        self.passive.len()
    }

    /// Add one input clause (an axiom or the negated goal) to `passive`.
    /// Terms inside `literals` must already have been built via
    /// `self.arena_mut()`.
    ///
    /// **Complexity:** O(clause weight) — dominated by `ClauseStore::insert`
    /// computing `weight`.
    pub fn add_input_clause(&mut self, literals: Vec<Literal>) -> ClauseId {
        let id = self.clause_store.insert(literals, InferenceInfo::input(), &self.arena);
        self.passive.push_back(id);
        id
    }

    /// Parse an S-expression-format problem (see `parser.rs`) and add every
    /// resulting clause as input. Terms are built directly into
    /// `self.arena_mut()`; predicate/function/constant names are interned
    /// into `symbols` (owned by the caller — typically reused afterward for
    /// `Clause::display`).
    ///
    /// **Algorithm:** thin wrapper — delegate parsing entirely to
    /// `parser::parse_problem`, then feed each resulting `Vec<Literal>`
    /// through `add_input_clause` one at a time.
    pub fn add_parsed_problem(
        &mut self,
        input: &str,
        symbols: &mut crate::term::SymbolTable
    ) -> Result<Vec<ClauseId>, crate::parser::ParseError> {
        let clauses = crate::parser::parse_problem(input, &mut self.arena, symbols)?;
        Ok(
            clauses
                .into_iter()
                .map(|lits| self.add_input_clause(lits))
                .collect()
        )
    }

    /// Walk a proof backward from `from` (typically a `SaturationResult::Proved`
    /// clause id) to all of its root input clauses. Thin delegation to
    /// `ClauseStore::proof_trace` — see that function's comments for the
    /// actual algorithm (post-order DFS over the derivation DAG).
    pub fn proof_trace(&self, from: ClauseId) -> Vec<ClauseId> {
        self.clause_store.proof_trace(from)
    }

    /// Insert the result of one inference into `clause_store`. Returns
    /// `(id, is_empty)` so the caller (`run`, below) can stop IMMEDIATELY
    /// upon deriving an empty clause, rather than waiting for it to cycle
    /// through `passive` on some future loop iteration.
    fn emit(&mut self, literals: Vec<Literal>, info: InferenceInfo) -> (ClauseId, bool) {
        let is_empty = literals.is_empty();
        let id = self.clause_store.insert(literals, info, &self.arena);
        (id, is_empty)
    }

    /// Run the given-clause loop. Stops when: (a) an empty clause is derived
    /// (`Proved`), (b) `passive` is exhausted (`Saturated`), or (c) the
    /// total clause count in `clause_store` reaches `max_clauses`
    /// (`ClauseLimitReached`) — a safety valve against infinite loops, since
    /// there's no simplification/subsumption yet (v0.2) to prune the search
    /// space.
    ///
    /// **Algorithm (see module-level doc for the numbered outline):**
    /// 1. Bail out with `ClauseLimitReached` if the clause budget is already
    ///    spent — checked at the TOP of every iteration, so this also
    ///    correctly catches the case where the input clauses ALONE already
    ///    exceed `max_clauses`, before the loop body ever runs once.
    /// 2. Pop the front of `passive`. Empty queue -> `Saturated`.
    /// 3. `.clone()` the given clause out of `clause_store` (see the
    ///    perf-tradeoff note inline below — this is a deliberate,
    ///    documented shortcut, not an oversight).
    /// 4. Empty clause -> `Proved` immediately.
    /// 5. `factor(&given, ...)` against itself; for each result, insert it
    ///    and check immediately for emptiness before deciding to queue it.
    /// 6. For every clause currently in `active` (snapshotted into a `Vec`
    ///    first — see the borrow-checker note inline below), `resolve(&given,
    ///    &active_clause, ...)`; same immediate-empty-check-then-queue
    ///    pattern.
    /// 7. Push `given_id` onto `active` — it's now available for FUTURE
    ///    given clauses to resolve against.
    /// 8. Loop.
    ///
    /// **Complexity per iteration:** O(|active|) resolve attempts, each
    /// itself O(|given| × |active_clause|) (see `inference::resolve`'s own
    /// complexity note) — so a single given-clause step costs
    /// O(|active| × average clause size²) in the worst case. This is the
    /// brute-force cost flagged for a discrimination-tree fix in v0.3 (see
    /// `inference.rs`'s TODO).
    pub fn run(&mut self, max_clauses: usize) -> SaturationResult {
        loop {
            if self.clause_store.len() >= max_clauses {
                return SaturationResult::ClauseLimitReached;
            }

            let given_id = match self.passive.pop_front() {
                Some(id) => id,
                None => {
                    return SaturationResult::Saturated;
                }
            };

            // Clone: avoids holding an immutable borrow of `self.clause_store`
            // (to read the given clause) at the same time as the `&mut
            // self.arena` that `resolve`/`factor` need to build substituted
            // terms. A deliberate simplicity-over-performance tradeoff for
            // v0.1 — a candidate for optimization in v0.3 IF cloning
            // `Clause` is ever shown to actually be a bottleneck (profile
            // before "fixing" this).
            let given: Clause = self.clause_store.get(given_id).clone();

            if given.is_empty() {
                return SaturationResult::Proved(given_id);
            }

            for (literals, info) in factor(&given, &mut self.arena) {
                let (id, is_empty) = self.emit(literals, info);
                if is_empty {
                    return SaturationResult::Proved(id);
                }
                self.passive.push_back(id);
            }

            // Snapshot `active`'s ids into an owned Vec first: iterating
            // `&self.active` directly while also calling `self.emit(...)`
            // (which needs `&mut self`) inside the loop body doesn't satisfy
            // the borrow checker (can't hold an immutable borrow of `self`
            // for iteration and a mutable borrow for `emit` at the same
            // time). Cloning the (small) id list sidesteps that; the actual
            // `Clause` data is still fetched fresh via `.clone()` per id
            // just below, same pattern/tradeoff as `given` above.
            let active_ids: Vec<ClauseId> = self.active.clone();
            for active_id in active_ids {
                let active_clause: Clause = self.clause_store.get(active_id).clone();
                for (literals, info) in resolve(
                    &given,
                    &active_clause,
                    &mut self.var_gen,
                    &mut self.arena
                ) {
                    let (id, is_empty) = self.emit(literals, info);
                    if is_empty {
                        return SaturationResult::Proved(id);
                    }
                    self.passive.push_back(id);
                }
            }

            self.active.push(given_id);
        }
    }
}

impl Default for Saturation {
    fn default() -> Self {
        Self::new()
    }
}

// TODO(v0.2 — given-clause selection): replace the plain `VecDeque` FIFO
// `passive` queue with an age-weight ratio priority queue (e.g. process N
// clauses by lowest weight for every 1 clause processed by age/FIFO order,
// a classic Vampire/E-prover strategy). This is the single biggest lever for
// proof-search quality on nontrivial problems — FIFO has no sense of which
// clauses are "promising". `Clause::age`/`Clause::weight` already exist and
// are already computed (see clause.rs) specifically in anticipation of this
// — they're just unused by `run` right now.

// TODO(v0.2 — simplification): before/after inserting a newly-derived clause
// into `passive`, this is where forward subsumption / tautology deletion
// checks would go (skip queuing a clause that's subsumed by something
// already in active/passive, or that's trivially a tautology like `P(a) |
// ~P(a)`). Right now EVERY generated clause gets queued unconditionally,
// including obvious dead ends — this is a large part of why the clause
// count grows fast even on small problems (see the worked example in the
// README/conversation history: clause `[4]` in the Socrates proof that gets
// derived but never used).

// TODO(v0.3 — perf): `given`/`active_clause` cloning (see inline comments
// above) is a real, measured-later-not-now cost once clauses get larger or
// the active set gets big. If profiling shows this matters, the fix is
// likely restructuring `Saturation`'s fields so `clause_store` and `arena`
// can be split-borrowed directly (e.g. accessor methods that borrow
// individual fields instead of going through `&self`/`&mut self` broadly),
// rather than reaching for `Rc<Clause>` as a first move.

// TODO(v0.4 — ML clause selection): `run`'s given-clause selection step
// (currently just `self.passive.pop_front()`) is exactly where a pluggable
// `ClauseSelector` trait would slot in (README §4.3) — swap FIFO/age-weight
// for a learned scoring function without touching anything else in this
// loop's structure.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Literal;
    use crate::term::SymbolTable;

    #[test]
    fn trivial_contradiction_is_proved() {
        let mut symbols = SymbolTable::new();
        let p = symbols.intern("P");
        let a = symbols.intern("a");

        let mut sat = Saturation::new();
        let a_term = sat.arena_mut().mk_app(a, &[]);

        sat.add_input_clause(vec![Literal::positive(p, vec![a_term])]);
        sat.add_input_clause(vec![Literal::negative(p, vec![a_term])]);

        let result = sat.run(1000);
        assert!(matches!(result, SaturationResult::Proved(_)));
    }

    #[test]
    fn proof_requiring_unification_of_variable_with_constant() {
        let mut symbols = SymbolTable::new();
        let p = symbols.intern("P");
        let a = symbols.intern("a");

        let mut sat = Saturation::new();
        let x = sat.arena_mut().mk_var(0);
        let a_term = sat.arena_mut().mk_app(a, &[]);

        // C1: P(X)   C2: ~P(a) -- requires unifying X=a, not an identical ground literal.
        sat.add_input_clause(vec![Literal::positive(p, vec![x])]);
        sat.add_input_clause(vec![Literal::negative(p, vec![a_term])]);

        let result = sat.run(1000);
        assert!(matches!(result, SaturationResult::Proved(_)));
    }

    #[test]
    fn syllogism_socrates_is_mortal_multi_step_proof() {
        // Classic: "All men are mortal. Socrates is a man. Therefore Socrates is mortal."
        // Proven via refutation: negate the goal, find a contradiction.
        //
        // CNF:
        //   C1: ~Man(X) | Mortal(X)     [Man(x) -> Mortal(x)]
        //   C2: Man(socrates)
        //   C3: ~Mortal(socrates)       [negated goal]
        //
        // Proof requires 2 chained resolution steps:
        //   resolve(C1, C2) -> Mortal(socrates)
        //   resolve(Mortal(socrates), C3) -> ⊥

        let mut symbols = SymbolTable::new();
        let man = symbols.intern("Man");
        let mortal = symbols.intern("Mortal");
        let socrates = symbols.intern("socrates");

        let mut sat = Saturation::new();
        let x = sat.arena_mut().mk_var(0);
        let socrates_term = sat.arena_mut().mk_app(socrates, &[]);

        let c1 = sat.add_input_clause(
            vec![Literal::negative(man, vec![x]), Literal::positive(mortal, vec![x])]
        );
        let c2 = sat.add_input_clause(vec![Literal::positive(man, vec![socrates_term])]);
        let c3 = sat.add_input_clause(vec![Literal::negative(mortal, vec![socrates_term])]);

        let result = sat.run(1000);
        let proved_id = match result {
            SaturationResult::Proved(id) => id,
            other => panic!("should be Proved, but got {other:?}"),
        };

        let trace = sat.proof_trace(proved_id);
        // All three input clauses must appear in the proof trace (all of them are actually
        // used to reach the contradiction).
        assert!(trace.contains(&c1));
        assert!(trace.contains(&c2));
        assert!(trace.contains(&c3));
        // The empty clause (final result) appears last in the trace (topological order).
        assert_eq!(*trace.last().unwrap(), proved_id);
        // This proof requires >3 clauses in the trace (3 inputs + 1 intermediate result + empty clause).
        assert!(trace.len() >= 4, "trace: {trace:?}");
    }

    #[test]
    fn independent_unit_clause_saturates_without_contradiction() {
        let mut symbols = SymbolTable::new();
        let p = symbols.intern("P");
        let a = symbols.intern("a");

        let mut sat = Saturation::new();
        let a_term = sat.arena_mut().mk_app(a, &[]);

        // Only one clause, nothing to resolve -- no contradiction
        // can possibly be found.
        sat.add_input_clause(vec![Literal::positive(p, vec![a_term])]);

        let result = sat.run(1000);
        assert_eq!(result, SaturationResult::Saturated);
    }

    #[test]
    fn clause_limit_stops_before_proving() {
        let mut symbols = SymbolTable::new();
        let p = symbols.intern("P");
        let q = symbols.intern("Q");
        let a = symbols.intern("a");
        let b = symbols.intern("b");

        let mut sat = Saturation::new();
        let a_term = sat.arena_mut().mk_app(a, &[]);
        let b_term = sat.arena_mut().mk_app(b, &[]);

        sat.add_input_clause(
            vec![Literal::positive(p, vec![a_term]), Literal::positive(q, vec![b_term])]
        );
        sat.add_input_clause(vec![Literal::negative(p, vec![a_term])]);
        sat.add_input_clause(vec![Literal::negative(q, vec![b_term])]);

        // max_clauses is extremely small -- the limit is already exceeded as soon as
        // the three input clauses are inserted, before the given-clause loop even has a chance to run.
        let result = sat.run(1);
        assert_eq!(result, SaturationResult::ClauseLimitReached);
    }

    #[test]
    fn multi_step_chain_resolution_via_intermediate_clause() {
        // C1: P(a) | Q(b)    C2: ~P(a)    C3: ~Q(b)
        // resolve(C1,C2) -> Q(b); resolve(Q(b), C3) -> ⊥
        let mut symbols = SymbolTable::new();
        let p = symbols.intern("P");
        let q = symbols.intern("Q");
        let a = symbols.intern("a");
        let b = symbols.intern("b");

        let mut sat = Saturation::new();
        let a_term = sat.arena_mut().mk_app(a, &[]);
        let b_term = sat.arena_mut().mk_app(b, &[]);

        sat.add_input_clause(
            vec![Literal::positive(p, vec![a_term]), Literal::positive(q, vec![b_term])]
        );
        sat.add_input_clause(vec![Literal::negative(p, vec![a_term])]);
        sat.add_input_clause(vec![Literal::negative(q, vec![b_term])]);

        let result = sat.run(1000);
        assert!(matches!(result, SaturationResult::Proved(_)));
    }
}
