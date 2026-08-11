//! proof_dag.rs — Certified Proof DAG extraction pass for Bear.
//!
//! Bear's `Clause` already IS a proof-DAG node: every clause carries its own
//! `id` and an `InferenceInfo { rule, parents }` describing how it was
//! derived. This module doesn't wrap that in anything new — it just treats
//! a `ClauseStore`'s worth of clauses as a DAG, validates the DAG structure,
//! and extracts the minimal sub-DAG that justifies the derivation of the
//! empty clause (⊥) — pruning every clause the solver generated during
//! search but never actually used in the refutation.
//!
//! Term data (`TermId`, `SymbolId`) is never interpreted here, same as
//! before — this module only ever moves ids around. Certificate
//! serialization needs to ship the relevant arena slice alongside the
//! extracted clauses; that's a separate pass (`collect_used_term_ids`,
//! not yet written).

use std::collections::{ HashMap, HashSet, VecDeque };
use std::fmt;
use crate::clause::{ Clause, ClauseId, InferenceRule };
use crate::unify::{ Substitution };
use crate::term::{ TermArena, TermId, TermData };

/// The full proof DAG — every clause the solver ever derived, keyed by id.
/// Just a thin view over a `ClauseStore`; doesn't own a `TermArena`.
#[derive(Debug, Clone, Default)]
pub struct ProofDag {
    clauses: HashMap<ClauseId, Clause>,
}

#[derive(Debug)]
pub enum DagError {
    UnknownParent {
        clause: ClauseId,
        missing: ClauseId,
    },
    Cycle(Vec<ClauseId>),
    NoBottom,
    DuplicateId(ClauseId),
    /// `inference.parents` disagrees with the parent(s) implied by
    /// `inference.rule` itself (e.g. `rule = Resolution{left: 1, right: 0,..}`
    /// but `parents = [1, 2]`). Two sources of truth for the same fact is a
    /// standing invitation for the emitter to desync them — this check
    /// exists to catch that class of bug before it ever reaches Lean.
    ParentsMismatch {
        clause: ClauseId,
        declared: Vec<ClauseId>,
        implied_by_rule: Vec<ClauseId>,
    },
}

impl fmt::Display for DagError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DagError::UnknownParent { clause, missing } => {
                write!(f, "clause {clause} references unknown parent {missing}")
            }
            DagError::Cycle(path) => write!(f, "cycle detected: {path:?}"),
            DagError::NoBottom => { write!(f, "no clause with empty literal set (⊥) found in DAG") }
            DagError::DuplicateId(id) => write!(f, "duplicate clause id {id}"),
            DagError::ParentsMismatch { clause, declared, implied_by_rule } =>
                write!(
                    f,
                    "clause {clause}: inference.parents = {declared:?} but rule implies {implied_by_rule:?}"
                ),
        }
    }
}

/// Parents implied by the rule variant itself, independent of
/// `InferenceInfo.parents`. Returns `None` for rules that don't yet encode
/// their own parents (the v0.2 equality rules) — `None` means "skip the
/// cross-check for this clause", not "no parents".
fn parents_implied_by_rule(rule: &InferenceRule) -> Option<Vec<ClauseId>> {
    match rule {
        InferenceRule::Input => Some(vec![]),
        InferenceRule::Resolution { left, right, .. } => Some(vec![*left, *right]),
        InferenceRule::Factoring { parent, .. } => Some(vec![*parent]),
        | InferenceRule::Superposition
        | InferenceRule::EqualityResolution
        | InferenceRule::EqualityFactoring
        | InferenceRule::Demodulation => None, // TODO(v0.2): not implemented yet
    }
}

fn same_parent_set(a: &[ClauseId], b: &[ClauseId]) -> bool {
    let sa: HashSet<_> = a.iter().collect();
    let sb: HashSet<_> = b.iter().collect();
    sa == sb
}

impl ProofDag {
    pub fn new() -> Self {
        Self { clauses: HashMap::new() }
    }

    /// Register a clause as the solver derives it. Call this once per
    /// clause, e.g. right where `ClauseStore` currently assigns it an id.
    pub fn insert(&mut self, clause: Clause) -> Result<(), DagError> {
        if self.clauses.contains_key(&clause.id) {
            return Err(DagError::DuplicateId(clause.id));
        }
        self.clauses.insert(clause.id, clause);
        Ok(())
    }

    pub fn get(&self, id: ClauseId) -> Option<&Clause> {
        self.clauses.get(&id)
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Structural well-formedness: every declared parent resolves to a real
    /// clause, `inference.parents` agrees with what the rule variant itself
    /// implies (where checkable), and the graph is acyclic. Logical
    /// soundness of each step is the Lean checker's job, not this module's.
    pub fn validate(&self) -> Result<(), DagError> {
        for clause in self.clauses.values() {
            for p in &clause.inference.parents {
                if !self.clauses.contains_key(p) {
                    return Err(DagError::UnknownParent { clause: clause.id, missing: *p });
                }
            }
            if let Some(implied) = parents_implied_by_rule(&clause.inference.rule) {
                if !same_parent_set(&clause.inference.parents, &implied) {
                    return Err(DagError::ParentsMismatch {
                        clause: clause.id,
                        declared: clause.inference.parents.clone(),
                        implied_by_rule: implied,
                    });
                }
            }
        }
        self.check_acyclic()
    }

    fn check_acyclic(&self) -> Result<(), DagError> {
        #[derive(Clone, Copy, PartialEq)]
        enum Mark {
            Unvisited,
            InProgress,
            Done,
        }
        let mut marks: HashMap<ClauseId, Mark> = self.clauses
            .keys()
            .map(|id| (*id, Mark::Unvisited))
            .collect();

        fn visit(
            id: ClauseId,
            clauses: &HashMap<ClauseId, Clause>,
            marks: &mut HashMap<ClauseId, Mark>,
            path: &mut Vec<ClauseId>
        ) -> Result<(), DagError> {
            match marks[&id] {
                Mark::Done => {
                    return Ok(());
                }
                Mark::InProgress => {
                    path.push(id);
                    return Err(DagError::Cycle(path.clone()));
                }
                Mark::Unvisited => {}
            }
            marks.insert(id, Mark::InProgress);
            path.push(id);
            for p in &clauses[&id].inference.parents {
                visit(*p, clauses, marks, path)?;
            }
            path.pop();
            marks.insert(id, Mark::Done);
            Ok(())
        }

        let mut path = Vec::new();
        for id in self.clauses.keys().copied().collect::<Vec<_>>() {
            visit(id, &self.clauses, &mut marks, &mut path)?;
        }
        Ok(())
    }

    /// Find the id of the empty clause (⊥), if present.
    pub fn find_bottom(&self) -> Option<ClauseId> {
        self.clauses
            .values()
            .find(|c| c.is_empty())
            .map(|c| c.id)
    }

    /// The extraction pass. Walks backward from `bottom_id` through
    /// `inference.parents` (BFS), keeps only reachable clauses, then
    /// returns them in topological order — parents strictly before children
    /// — so the Lean checker can process the certificate as a straight-line
    /// list with no forward references.
    pub fn extract_relevant(&self, bottom_id: ClauseId) -> Result<Vec<Clause>, DagError> {
        if !self.clauses.contains_key(&bottom_id) {
            return Err(DagError::NoBottom);
        }

        let mut reachable: HashSet<ClauseId> = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(bottom_id);
        reachable.insert(bottom_id);
        while let Some(id) = queue.pop_front() {
            for p in &self.clauses[&id].inference.parents {
                if reachable.insert(*p) {
                    queue.push_back(*p);
                }
            }
        }

        let mut order = Vec::with_capacity(reachable.len());
        let mut visited = HashSet::new();

        fn dfs(
            id: ClauseId,
            clauses: &HashMap<ClauseId, Clause>,
            reachable: &HashSet<ClauseId>,
            visited: &mut HashSet<ClauseId>,
            order: &mut Vec<ClauseId>
        ) {
            if !visited.insert(id) {
                return;
            }
            for p in &clauses[&id].inference.parents {
                if reachable.contains(p) {
                    dfs(*p, clauses, reachable, visited, order);
                }
            }
            order.push(id);
        }

        for id in &reachable {
            dfs(*id, &self.clauses, &reachable, &mut visited, &mut order);
        }

        Ok(
            order
                .into_iter()
                .map(|id| self.clauses[&id].clone())
                .collect()
        )
    }

    /// Convenience wrapper: validate, find ⊥ automatically, extract.
    /// Call this right after the solver reports PROVED.
    pub fn certificate(&self) -> Result<Vec<Clause>, DagError> {
        self.validate()?;
        let bottom = self.find_bottom().ok_or(DagError::NoBottom)?;
        self.extract_relevant(bottom)
    }
}

// ---------------------------------------------------------------------
// collect_used_term_ids
// ---------------------------------------------------------------------

/// Returns the substitution attached to a rule, if it has one. `Input`
/// clauses and the not-yet-implemented v0.2 rules have none.
fn substitution_of(rule: &InferenceRule) -> Option<&Substitution> {
    match rule {
        InferenceRule::Resolution { unifier, .. } => Some(unifier),
        InferenceRule::Factoring { unifier, .. } => Some(unifier),
        | InferenceRule::Input
        | InferenceRule::Superposition
        | InferenceRule::EqualityResolution
        | InferenceRule::EqualityFactoring
        | InferenceRule::Demodulation => None,
    }
}

/// Walks an extracted certificate (the output of `ProofDag::certificate` /
/// `extract_relevant`) and returns the closure of every `TermId` that needs
/// to be serialized alongside it for a `.beardag` certificate to be
/// self-contained: every literal argument, every substitution binding
/// target, and — recursively — every subterm reachable from those through
/// `App` arguments.
///
/// Without this closure, a certificate would ship top-level `TermId`s that
/// point into an arena the reader (the Lean side) doesn't have, and
/// `App(sym, start, len)` nodes for compound terms would be unresolvable:
/// the reader needs every subterm in the arena slice too, not just the ids
/// mentioned directly in a `Literal` or `Substitution`.
///
/// Call this with the SAME arena the solver used to build the certificate's
/// clauses — `TermId`s are only meaningful relative to the arena that
/// produced them.
pub fn collect_used_term_ids(clauses: &[Clause], arena: &TermArena) -> HashSet<TermId> {
    let mut used = HashSet::new();
    let mut stack = Vec::new();

    for c in clauses {
        for lit in &c.literals {
            stack.extend(lit.args.iter().copied());
        }
        if let Some(sub) = substitution_of(&c.inference.rule) {
            for (_, t) in sub.iter() {
                stack.push(t);
            }
        }
    }

    while let Some(t) = stack.pop() {
        if used.insert(t) {
            if let TermData::App(..) = arena.get(t) {
                stack.extend(arena.args(t).iter().copied());
            }
        }
    }

    used
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{ SymbolId, TermId };
    use crate::clause::{ InferenceInfo, Literal };
    use crate::unify::Substitution;
    use crate::term::{ TermArena };

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

    /// Socrates DAG plus one decoy clause (id 4) the search explored but
    /// the refutation never uses.
    fn build_socrates_dag() -> ProofDag {
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

        let mut sub = HashMap::new();
        sub.insert(0u32, socrates);
        dag.insert(
            resolution_clause(
                3,
                vec![lit(true, p_mortal, vec![socrates])],
                1,
                0,
                0,
                0,
                Substitution::default()
            )
        ).unwrap();

        // decoy: factoring clause, never reachable from bottom
        dag.insert(Clause {
            id: 4,
            literals: vec![lit(true, p_man, vec![x0])],
            age: 0,
            weight: 0,
            inference: InferenceInfo {
                rule: InferenceRule::Factoring {
                    parent: 0,
                    lit_a: 0,
                    lit_b: 0,
                    unifier: Substitution::default(),
                },
                parents: vec![0],
            },
        }).unwrap();

        dag.insert(resolution_clause(5, vec![], 3, 0, 2, 0, Substitution::default())).unwrap();

        dag
    }

    /// A tiny DAG whose only point is to have a substitution binding that
    /// targets a COMPOUND term (`f(a, b)`), so `collect_used_term_ids` has
    /// something non-trivial to recurse into. Shape:
    ///   [0] p(X)            (input)
    ///   [1] ~p(f(a, b))      (input, negated goal)
    ///   [2] ⊥  (Resolution <- [0, 1], unifier: X -> f(a, b))
    /// Also throws in an unrelated term (`unused_const`) built in the same
    /// arena but never referenced by any clause, to prove it's correctly
    /// excluded from the collected set.
    fn build_dag_with_nested_terms() -> (ProofDag, TermArena, TermId, TermId, TermId, TermId) {
        let mut arena = TermArena::new();
        let mut syms = MiniSymbols::new();

        let p_p = syms.intern("p");
        let s_f = syms.intern("f");
        let s_a = syms.intern("a");
        let s_b = syms.intern("b");
        let s_unused = syms.intern("unused");

        let x0 = arena.mk_var(0);
        let a = arena.mk_const(s_a);
        let b = arena.mk_const(s_b);
        let fab = arena.mk_app(s_f, &[a, b]);
        let unused_const = arena.mk_const(s_unused); // never referenced by any clause

        let mut dag = ProofDag::new();

        dag.insert(input_clause(0, vec![lit(true, p_p, vec![x0])])).unwrap();
        dag.insert(input_clause(1, vec![lit(false, p_p, vec![fab])])).unwrap();

        let mut sub = Substitution::new();
        sub.bind(0u32, fab);
        dag.insert(resolution_clause(2, vec![], 0, 0, 1, 0, sub)).unwrap();

        (dag, arena, fab, a, b, unused_const)
    }

    #[test]
    fn collect_used_term_ids_recurses_into_compound_terms_and_excludes_unused() {
        let (dag, arena, fab, a, b, unused_const) = build_dag_with_nested_terms();
        let cert = dag.certificate().expect("certificate extraction failed");
        let used = collect_used_term_ids(&cert, &arena);

        // fab = f(a, b) is referenced directly (it's the substitution's
        // binding target); a and b are only reachable by recursing into
        // fab's App args — this is the whole point of the closure walk.
        assert!(used.contains(&fab), "compound substitution target missing from closure");
        assert!(used.contains(&a), "subterm `a` missing: closure didn't recurse into App args");
        assert!(used.contains(&b), "subterm `b` missing: closure didn't recurse into App args");

        assert!(
            !used.contains(&unused_const),
            "collect_used_term_ids pulled in a term no clause ever referenced"
        );
    }

    #[test]
    fn validates_clean() {
        assert!(build_socrates_dag().validate().is_ok());
    }

    #[test]
    fn finds_bottom() {
        assert_eq!(build_socrates_dag().find_bottom(), Some(5));
    }

    #[test]
    fn extraction_prunes_the_decoy_and_orders_topologically() {
        let dag = build_socrates_dag();
        let cert = dag.certificate().expect("certificate extraction failed");
        let ids: Vec<ClauseId> = cert
            .iter()
            .map(|c| c.id)
            .collect();

        assert!(!ids.contains(&4), "pruning failed: decoy clause leaked into certificate");
        assert_eq!(ids.len(), 5);

        let pos: HashMap<ClauseId, usize> = ids
            .iter()
            .enumerate()
            .map(|(i, id)| (*id, i))
            .collect();
        for c in &cert {
            for p in &c.inference.parents {
                assert!(pos[p] < pos[&c.id], "parent {p} must precede child {}", c.id);
            }
        }
        assert!(cert.last().unwrap().is_empty());
    }

    #[test]
    fn detects_dangling_parent() {
        let mut dag = ProofDag::new();
        dag.insert(resolution_clause(0, vec![], 99, 0, 1, 0, Substitution::default())).unwrap();
        match dag.validate() {
            Err(DagError::UnknownParent { missing: 99, .. }) => {}
            other => panic!("expected UnknownParent(99), got {other:?}"),
        }
    }

    #[test]
    fn detects_cycle() {
        let mut dag = ProofDag::new();
        dag.insert(Clause {
            id: 0,
            literals: vec![],
            age: 0,
            weight: 0,
            inference: InferenceInfo {
                rule: InferenceRule::Factoring {
                    parent: 1,
                    lit_a: 0,
                    lit_b: 0,
                    unifier: Substitution::default(),
                },
                parents: vec![1],
            },
        }).unwrap();
        dag.insert(Clause {
            id: 1,
            literals: vec![],
            age: 0,
            weight: 0,
            inference: InferenceInfo {
                rule: InferenceRule::Factoring {
                    parent: 0,
                    lit_a: 0,
                    lit_b: 0,
                    unifier: Substitution::default(),
                },
                parents: vec![0],
            },
        }).unwrap();
        assert!(matches!(dag.validate(), Err(DagError::Cycle(_))));
    }

    #[test]
    fn detects_parents_mismatch() {
        // rule says parents are [1, 0], but inference.parents claims [1, 2]
        // (e.g. an emitter bug where the wrong clause id was recorded).
        let mut dag = ProofDag::new();
        dag.insert(input_clause(0, vec![])).unwrap();
        dag.insert(input_clause(1, vec![])).unwrap();
        dag.insert(input_clause(2, vec![])).unwrap();
        dag.insert(Clause {
            id: 3,
            literals: vec![],
            age: 0,
            weight: 0,
            inference: InferenceInfo {
                rule: InferenceRule::Resolution {
                    left: 1,
                    left_lit: 0,
                    right: 0,
                    right_lit: 0,
                    unifier: Substitution::default(),
                },
                parents: vec![1, 2], // desynced on purpose
            },
        }).unwrap();
        assert!(matches!(dag.validate(), Err(DagError::ParentsMismatch { clause: 3, .. })));
    }
}
