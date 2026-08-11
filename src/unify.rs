//! Substitution and Robinson-style unification for first-order terms.
//!
//! `unify` (and everything it calls) only ever READS `TermArena`
//! (`&TermArena`, never `&mut`) — unification never modifies terms already
//! in the arena, it only fills in a `Substitution` (a variable -> term
//! mapping). This matters for *structure sharing*: the same term can be
//! reused by many different clauses/inference attempts without any of them
//! stepping on each other.
//!
//! `Substitution::apply`, in contrast, DOES need `&mut TermArena`, because
//! it actually *constructs* new terms as the result of substitution (via
//! `mk_app`, so the result stays properly interned).
//!
//! **Current substitution representation:** `HashMap<VarId, TermId>` with
//! manual chain-following in `resolve()`. This is good enough for the v0.1
//! MVP; swapping to a union-find structure (cheaper `resolve`, path
//! compression) is on the v0.3 roadmap (README §2) — see the TODO on
//! `Substitution` below for specifics.

use std::collections::HashMap;

use crate::clause::Literal;
use crate::term::{ TermArena, TermData, TermId, VarId };

/// A variable -> term mapping. Bindings can chain (`X -> Y`, `Y -> a`);
/// `resolve()` follows this chain until it hits a non-variable term or an
/// unbound variable.
#[derive(Debug, Default, Clone)]
pub struct Substitution {
    bindings: HashMap<VarId, TermId>,
}

impl Substitution {
    pub fn new() -> Self {
        Self { bindings: HashMap::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Record a binding directly, no validation performed (no occurs-check,
    /// no check whether `v` was already bound — this is the low-level
    /// primitive `unify` builds on top of). If `v` already had a binding,
    /// it's silently overwritten.
    ///
    /// **Complexity:** O(1) average (`HashMap` insert).
    pub fn bind(&mut self, v: VarId, t: TermId) {
        self.bindings.insert(v, t);
    }

    pub fn binding_of(&self, v: VarId) -> Option<TermId> {
        self.bindings.get(&v).copied()
    }

    /// Follow the binding chain starting at `term` until reaching either a
    /// non-variable term, or a variable with no binding yet. This does NOT
    /// recurse into subterms (it's not a full `apply`) — it only "peels"
    /// the root, which is all `unify` needs to always work against the most
    /// up-to-date representative of a term.
    ///
    /// **Algorithm:** classic union-find-style "find" loop (minus the
    /// tree/rank structure union-find normally has — see TODO below): keep
    /// following `Var(v) -> binding_of(v)` while the current term is a bound
    /// variable; stop at the first `App` or unbound `Var`.
    ///
    /// **Cycle detection (`visited`)** is a defense-in-depth safety net,
    /// NOT the primary way cycles get prevented. A binding like `X -> X`
    /// (self-loop) actually happened once during development — see
    /// `inference::rename_apart`'s own comments for how that bug was fixed
    /// AT THE SOURCE. `visited` here just guarantees that IF some circular
    /// binding ever slips through some other path (e.g. occurs-check
    /// manually disabled, or a future bug), `resolve` terminates instead of
    /// hanging forever, rather than actually preventing bad bindings from
    /// being created in the first place.
    ///
    /// **Complexity:** O(chain length) time, O(chain length) extra space for
    /// `visited`. Chain length is normally tiny (a handful of hops), but
    /// there's no path compression — repeatedly resolving through the same
    /// long chain redoes the whole walk every time. See TODO below.
    pub fn resolve(&self, term: TermId, arena: &TermArena) -> TermId {
        let mut current = term;
        let mut visited: std::collections::HashSet<VarId> = std::collections::HashSet::new();
        loop {
            match arena.get(current) {
                TermData::Var(v) => {
                    if !visited.insert(v) {
                        return current; // cycle detected, bail out instead of looping forever
                    }
                    match self.binding_of(v) {
                        Some(next) => {
                            current = next;
                        }
                        None => {
                            return current;
                        }
                    }
                }
                TermData::App(..) => {
                    return current;
                }
            }
        }
    }

    /// Fully, recursively apply this substitution to `term`, producing a
    /// brand-new term in `arena` (still properly interned, since it's built
    /// via `mk_app`/implicitly via `resolve`'s use of `arena.get`).
    ///
    /// **Algorithm:**
    /// 1. `resolve(term)` to peel off the root (handles the "this whole
    ///    term IS a bound variable" case in one step).
    /// 2. If the result is still a `Var` (unbound) -> return as-is, nothing
    ///    more to do.
    /// 3. If it's an `App` with no args (a constant) -> return as-is, no
    ///    substitution can possibly apply inside a constant.
    /// 4. Otherwise, recursively `apply` to EVERY argument, then rebuild via
    ///    `arena.mk_app` with the (possibly changed) argument list.
    ///
    /// If `term` isn't affected by the substitution at all (e.g. it's a
    /// ground term with no variables anywhere in it), `apply` returns the
    /// exact same `TermId` it was given — rebuilding an identical term
    /// through `mk_app` just hits the interning cache and hands back the
    /// same id, no new allocation happens (see `TermArena::mk_app`).
    ///
    /// **Complexity:** O(size of the resulting term) — one recursive call
    /// per node, each doing an O(arity) `Vec` collect + one `mk_app` call.
    pub fn apply(&self, term: TermId, arena: &mut TermArena) -> TermId {
        let resolved = self.resolve(term, arena);
        match arena.get(resolved) {
            TermData::Var(_) => resolved,
            TermData::App(symbol, _, _) => {
                let args: Vec<TermId> = arena.args(resolved).to_vec();
                if args.is_empty() {
                    return resolved; // constant, nothing inside it to substitute
                }
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.apply(a, arena))
                    .collect();
                arena.mk_app(symbol, &new_args)
            }
        }
    }

    /// Occurs-check: does variable `v` appear anywhere inside `term`, after
    /// resolving through the current substitution?
    ///
    /// **Why this matters:** without this check, unifying `X` with `f(X)`
    /// would produce the binding `X -> f(X)`. Trying to `apply` that binding
    /// would recurse forever (`f(X)` contains `X`, which resolves back to
    /// `f(X)`, which contains `X`, ...) — it describes an "infinite" term
    /// that can never actually be built. `occurs` is what `unify` calls
    /// BEFORE creating a binding, to reject exactly this situation.
    ///
    /// **Algorithm:** resolve `term` first (so we check against its current
    /// representative, not a stale unbound variable), then recursively scan
    /// every subterm for an occurrence of `v`.
    ///
    /// **Complexity:** O(size of `term`) after resolving.
    fn occurs(&self, v: VarId, term: TermId, arena: &TermArena) -> bool {
        let resolved = self.resolve(term, arena);
        match arena.get(resolved) {
            TermData::Var(v2) => v2 == v,
            TermData::App(..) =>
                arena
                    .args(resolved)
                    .iter()
                    .any(|&a| self.occurs(v, a, arena)),
        }
    }
}

// TODO(v0.3 — perf): replace the `HashMap<VarId, TermId>` + manual chasing
// in `resolve()` with a proper union-find (disjoint-set) structure with path
// compression. Right now, resolving through a long binding chain redoes the
// full walk every single call — union-find with path compression would
// flatten the chain as a side effect of the FIRST resolve, making every
// subsequent resolve of the same variable close to O(1) (amortized, inverse-
// Ackermann). This is exactly the kind of hot-path cost that starts to
// matter once problems get big enough that `unify` is called thousands of
// times per given-clause iteration. Don't do this speculatively — profile
// first once v0.2 equality reasoning is in and real problems are being run,
// confirm this is actually where time goes before rewriting it.

/// Unify two terms, with occurs-check ON (the safe default — see
/// `unify_with_occurs_check` for what turning it off risks).
///
/// Returns `true` and fills in `subst` on success. **On failure, `subst` may
/// already contain SOME bindings** recorded by recursive calls before the
/// failure point — this function does NOT roll those back. Callers that need
/// a clean slate per attempt must pass in a fresh `Substitution` (this is
/// exactly what `inference::resolve`/`factor` do: a brand new `Substitution`
/// per candidate literal pair, never reused across attempts — see the
/// comments there).
pub fn unify(t1: TermId, t2: TermId, arena: &TermArena, subst: &mut Substitution) -> bool {
    unify_with_occurs_check(t1, t2, arena, subst, true)
}

/// Same as `unify`, but lets you disable the occurs-check
/// (`occurs_check = false`). Disabling it makes unification faster (skips
/// the extra traversal in `Substitution::occurs`) but can produce a circular
/// substitution that makes `Substitution::apply` loop forever. Don't turn
/// this off unless you've independently guaranteed the inputs can never
/// produce a circular binding.
///
/// **Algorithm (classic Robinson unification, recursive):**
/// 1. Resolve both terms through the current `subst` first (so we're always
///    comparing against the most up-to-date representative of each side,
///    not a stale reference).
/// 2. If they resolved to the exact same `TermId` -> already unified, done
///    (this also covers "two identical ground terms", for free, thanks to
///    interning — no need for a special case).
/// 3. `Var` / `Var` -> bind one to the other arbitrarily (first argument's
///    variable gets bound to the second's resolved term).
/// 4. `Var` / `App` (either order) -> occurs-check (if enabled), then bind
///    the variable to the application term.
/// 5. `App` / `App` -> symbols must match exactly, arities must match
///    (should always hold together if symbols match, but checked
///    defensively anyway), then recursively unify EVERY argument pair
///    left-to-right, threading the SAME `subst` through all of them (so a
///    binding made while unifying argument 1 is visible/enforced when
///    unifying argument 2 — this is what makes `f(X, X)` vs `f(a, b)`
///    correctly FAIL, since X can't be bound to both `a` and `b`).
///
/// **Complexity:** O(size of the smaller resulting substituted term) in the
/// typical case; worst case (repeated shared variables across many
/// arguments) can revisit the same subterm structure multiple times since
/// there's no memoization — acceptable for v0.1, revisit if it becomes a
/// bottleneck.
pub fn unify_with_occurs_check(
    t1: TermId,
    t2: TermId,
    arena: &TermArena,
    subst: &mut Substitution,
    occurs_check: bool
) -> bool {
    let r1 = subst.resolve(t1, arena);
    let r2 = subst.resolve(t2, arena);

    if r1 == r2 {
        return true; // includes the "two identical ground terms" case, free via interning
    }

    match (arena.get(r1), arena.get(r2)) {
        (TermData::Var(v1), TermData::Var(_)) => {
            subst.bind(v1, r2);
            true
        }
        (TermData::Var(v1), TermData::App(..)) => {
            if occurs_check && subst.occurs(v1, r2, arena) {
                return false;
            }
            subst.bind(v1, r2);
            true
        }
        (TermData::App(..), TermData::Var(v2)) => {
            if occurs_check && subst.occurs(v2, r1, arena) {
                return false;
            }
            subst.bind(v2, r1);
            true
        }
        (TermData::App(s1, _, _), TermData::App(s2, _, _)) => {
            if s1 != s2 {
                return false;
            }
            let args1: Vec<TermId> = arena.args(r1).to_vec();
            let args2: Vec<TermId> = arena.args(r2).to_vec();
            if args1.len() != args2.len() {
                return false; // shouldn't happen if symbols match & arity is consistent, but defensive
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                if !unify_with_occurs_check(*a1, *a2, arena, subst, occurs_check) {
                    return false;
                }
            }
            true
        }
    }
}

// TODO(v0.3 — perf, same root cause as TermArena::mk_app): `args1.to_vec()` /
// `args2.to_vec()` here clone the argument slices before iterating. Could be
// avoided by restructuring to iterate `arena.args(r1)` and `arena.args(r2)`
// directly via indices instead of cloning first — the current clone exists
// only because holding a borrow of `arena` across the recursive
// `unify_with_occurs_check` call (which also borrows `arena`) gets awkward
// with the borrow checker. Worth revisiting alongside the `mk_app` interning
// fix, since both are instances of the same underlying "avoid needless Vec
// clone in a hot path" problem.

/// Unify two literals: predicate and arity must match, then every argument
/// pair is unified using the SAME `subst` (built up cumulatively — if a
/// later argument fails to unify, bindings from earlier arguments remain
/// recorded in `subst`, so callers should use a FRESH `Substitution` per
/// literal-pair attempt, same caveat as `unify`).
///
/// Polarity is deliberately NOT checked here — it's the caller's job
/// (`inference::resolve`/`factor`) to decide which polarity combinations are
/// valid for their respective rule (Resolution wants opposite polarities,
/// Factoring wants the same polarity).
///
/// **Complexity:** O(arity) unify calls, each O(size of that argument) —
/// see `unify_with_occurs_check` above.
pub fn unify_literals(
    l1: &Literal,
    l2: &Literal,
    arena: &TermArena,
    subst: &mut Substitution
) -> bool {
    if l1.predicate != l2.predicate || l1.args.len() != l2.args.len() {
        return false;
    }
    for (&a1, &a2) in l1.args.iter().zip(l2.args.iter()) {
        if !unify(a1, a2, arena, subst) {
            return false;
        }
    }
    true
}

// TODO(v0.2 — equality reasoning): Superposition needs a notion of matching
// (one-directional: does term A become term B under SOME substitution,
// without touching B's variables) in addition to full unification
// (bidirectional). `unify`/`unify_with_occurs_check` as written always treat
// both sides symmetrically. A separate `match_term`/`matches` function will
// likely be needed alongside these — don't try to force it into the existing
// `unify` by adding more flags, it's a conceptually different operation
// (used for demodulation: "can I rewrite using this equation here").

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{ SymbolTable };

    struct Fixture {
        symbols: SymbolTable,
        f: u32, // f/1
        g: u32, // g/2
        a: u32, // constant a
        b: u32, // constant b
    }

    fn fixture() -> Fixture {
        let mut symbols = SymbolTable::new();
        let f = symbols.intern("f");
        let g = symbols.intern("g");
        let a = symbols.intern("a");
        let b = symbols.intern("b");
        Fixture { symbols, f, g, a, b }
    }

    #[test]
    fn unify_two_distinct_variables_binds_one_to_other() {
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let y = arena.mk_var(1);
        let mut subst = Substitution::new();

        assert!(unify(x, y, &arena, &mut subst));
        assert_eq!(subst.len(), 1);

        assert_eq!(subst.resolve(x, &arena), subst.resolve(y, &arena));
    }

    #[test]
    fn unify_same_variable_is_trivially_successful_with_no_new_binding() {
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let mut subst = Substitution::new();

        assert!(unify(x, x, &arena, &mut subst));
        assert!(subst.is_empty(), "unifying X with X itself does not require a new binding");
    }

    #[test]
    fn unify_variable_with_constant() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let a = arena.mk_app(fx.a, &[]);
        let mut subst = Substitution::new();

        assert!(unify(x, a, &arena, &mut subst));
        assert_eq!(subst.resolve(x, &arena), a);
    }

    #[test]
    fn unify_constant_with_variable_symmetric() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let a = arena.mk_app(fx.a, &[]);
        let mut subst = Substitution::new();

        assert!(unify(a, x, &arena, &mut subst));
        assert_eq!(subst.resolve(x, &arena), a);
    }

    #[test]
    fn unify_identical_ground_constants_succeeds_without_binding() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a1 = arena.mk_app(fx.a, &[]);
        let a2 = arena.mk_app(fx.a, &[]); // interned -> TermId same with a1
        let mut subst = Substitution::new();

        assert!(unify(a1, a2, &arena, &mut subst));
        assert!(subst.is_empty());
    }

    #[test]
    fn unify_different_ground_constants_fails() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);
        let mut subst = Substitution::new();

        assert!(!unify(a, b, &arena, &mut subst));
    }

    #[test]
    fn unify_compound_terms_with_matching_structure() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let y = arena.mk_var(1);
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // g(X, a) unify g(b, Y) => X = b, Y = a
        let t1 = arena.mk_app(fx.g, &[x, a]);
        let t2 = arena.mk_app(fx.g, &[b, y]);
        let mut subst = Substitution::new();

        assert!(unify(t1, t2, &arena, &mut subst));
        assert_eq!(subst.resolve(x, &arena), b);
        assert_eq!(subst.resolve(y, &arena), a);
    }

    #[test]
    fn unify_fails_on_different_symbol() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let fa = arena.mk_app(fx.f, &[a]);
        let ga = arena.mk_app(fx.g, &[a, a]);
        let mut subst = Substitution::new();

        assert!(!unify(fa, ga, &arena, &mut subst));
    }

    #[test]
    fn unify_fails_on_different_arity_same_symbol_family() {
        // This case is purely to ensure an argument length mismatch is rejected;
        // in practice, symbols with different arities usually already have different SymbolIds,
        // but we test directly at the argument level just in case.
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let fa = arena.mk_app(fx.f, &[a]); // f/1
        let mut subst = Substitution::new();

        // f(a) vs f(a, a) using the same symbol but different arities -> must still fail
        // (here we force the same symbol as symbol f, but with different argument lengths).
        let fa_a = arena.mk_app(fx.f, &[a, a]);
        assert!(!unify(fa, fa_a, &arena, &mut subst));
    }

    #[test]
    fn unify_repeated_variable_forces_consistent_binding() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // f(X, X) vs f(a, a) -> X should be consistent = a -> success
        let t1 = arena.mk_app(fx.g, &[x, x]);
        let t2_ok = arena.mk_app(fx.g, &[a, a]);
        let mut subst_ok = Substitution::new();
        assert!(unify(t1, t2_ok, &arena, &mut subst_ok));
        assert_eq!(subst_ok.resolve(x, &arena), a);

        // f(X, X) vs f(a, b) -> X should be a AND b at once -> failed
        let t2_fail = arena.mk_app(fx.g, &[a, b]);
        let mut subst_fail = Substitution::new();
        assert!(!unify(t1, t2_fail, &arena, &mut subst_fail));
    }

    #[test]
    fn occurs_check_rejects_circular_binding() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let fx_term = arena.mk_app(fx.f, &[x]); // f(X)
        let mut subst = Substitution::new();

        // X unify f(X) -> occurs-check must reject (X occurs inside f(X))
        assert!(!unify(x, fx_term, &arena, &mut subst));
    }

    #[test]
    fn occurs_check_disabled_allows_circular_binding_to_be_recorded() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let fx_term = arena.mk_app(fx.f, &[x]);
        let mut subst = Substitution::new();

        // With occurs_check=false, unification "succeeds" (a circular binding
        // is recorded). We INTENTIONALLY do not call `apply` here because it would
        // cause an infinite loop — this is purely to prove that the occurs_check flag indeed
        // changes behavior, not to suggest its use under normal conditions.
        assert!(unify_with_occurs_check(x, fx_term, &arena, &mut subst, false));
        assert_eq!(subst.binding_of(0), Some(fx_term));
    }

    #[test]
    fn resolve_follows_chained_bindings() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let y = arena.mk_var(1);
        let a = arena.mk_app(fx.a, &[]);
        let mut subst = Substitution::new();

        // Build a manual chain: X -> Y, Y -> a
        subst.bind(0, y);
        subst.bind(1, a);

        assert_eq!(subst.resolve(x, &arena), a);
    }

    #[test]
    fn apply_builds_substituted_term_through_chained_binding() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let y = arena.mk_var(1);
        let a = arena.mk_app(fx.a, &[]);
        let mut subst = Substitution::new();
        subst.bind(0, y);
        subst.bind(1, a);

        // f(X) with X -> Y -> a, applying must result in f(a)
        let fx_term = arena.mk_app(fx.f, &[x]);
        let result = subst.apply(fx_term, &mut arena);

        let expected = arena.mk_app(fx.f, &[a]); // f(a) directly
        assert_eq!(result, expected, "apply must produce the same (interned) term as f(a)");
        assert_eq!(arena.display(result, &fx.symbols), "f(a)");
    }

    #[test]
    fn apply_on_ground_term_is_identity() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let ga = arena.mk_app(fx.g, &[a, a]);
        let subst = Substitution::new(); // empty, no bindings

        let result = subst.apply(ga, &mut arena);
        assert_eq!(result, ga, "a ground term without variables must remain unchanged");
    }

    #[test]
    fn apply_substitutes_nested_occurrences_of_same_variable() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let a = arena.mk_app(fx.a, &[]);
        let mut subst = Substitution::new();
        subst.bind(0, a);

        // g(X, X) with X -> a should become g(a, a), and both arguments
        // are the same TermId `a` (proof that subterm sharing is preserved after apply)
        let gxx = arena.mk_app(fx.g, &[x, x]);
        let result = subst.apply(gxx, &mut arena);
        let args = arena.args(result).to_vec();

        assert_eq!(args, vec![a, a]);
        assert_eq!(arena.display(result, &fx.symbols), "g(a, a)");
    }

    #[test]
    fn unify_and_apply_end_to_end() {
        // Realistic scenario: unify g(X, a) with g(b, Y), then apply the resulting
        // substitution to g(X, Y) itself -> must become g(b, a).
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(0);
        let y = arena.mk_var(1);
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        let t1 = arena.mk_app(fx.g, &[x, a]);
        let t2 = arena.mk_app(fx.g, &[b, y]);
        let mut subst = Substitution::new();
        assert!(unify(t1, t2, &arena, &mut subst));

        let xy = arena.mk_app(fx.g, &[x, y]);
        let result = subst.apply(xy, &mut arena);
        let expected = arena.mk_app(fx.g, &[b, a]);

        assert_eq!(result, expected);
        assert_eq!(arena.display(result, &fx.symbols), "g(b, a)");
    }
}
