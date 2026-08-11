//! Term representation for the ATP.
//!
//! # The core idea: hash-consing (structural interning)
//!
//! Every term lives in one `TermArena` per problem/session, and is addressed
//! by a `TermId` (a plain `u32` index) — never by pointer or `Rc`. Whenever
//! you build a term that is *structurally identical* to one that already
//! exists in the arena, you get back the SAME `TermId`, not a new one. This
//! technique is called **hash-consing**: every "cons" (construction) is
//! checked against a hash table first, and reused if an identical structure
//! already exists.
//!
//! Two consequences fall out of this for free:
//! 1. **O(1) structural equality.** Two terms are structurally equal
//!    if and only if their `TermId`s are equal. You never need to walk the
//!    tree to compare terms.
//! 2. **Automatic subterm sharing.** If `f(a, a)` and `g(a)` both use `a`,
//!    there is only ONE `a` in memory, referenced twice. You get this
//!    sharing without doing anything special — it's just a side effect of
//!    always looking up before inserting.
//!
//! This is a deliberately simple, correctness-first v0.1 implementation.
//! See the `// TODO(vX.Y)` comments scattered through this file for what's
//! known to be suboptimal and what the plan is to fix it later — read those
//! before touching performance-sensitive code here.

use std::collections::HashMap;

/// Id for a function/predicate/constant symbol (e.g. `f`, `a`, `P`). Just an
/// index into `SymbolTable`, has no meaning on its own.
pub type SymbolId = u32;

/// Id for a variable. IMPORTANT: this is scoped to a single clause, NOT
/// globally unique across the whole problem. Two different clauses can both
/// have a "variable 0" and they mean completely different things — nothing
/// in `TermArena` itself prevents or resolves that collision. Making sure
/// two clauses don't get their variables accidentally conflated is handled
/// OUTSIDE this file, by `inference::rename_apart` right before Resolution
/// runs.
pub type VarId = u32;

/// Index of a term inside a `TermArena`. Cheap to copy, cheap to hash, no
/// lifetime attached to it (unlike `&Term` would be) — that's the whole
/// point of the arena+index design instead of `Rc<Term>` trees.
pub type TermId = u32;

/// The actual data stored for one term, flat in `TermArena::terms`.
///
/// For `App`, the arguments are NOT stored inline as a `Vec<TermId>` on this
/// enum. Instead they're stored as a `(start, len)` range pointing into
/// `TermArena::args_pool`, a single shared flat buffer for ALL terms' args.
/// This avoids giving every single term its own separate heap allocation
/// for its argument list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TermData {
    /// A variable, identified by `VarId`.
    Var(VarId),
    /// A function/predicate/constant application: `symbol(args...)`.
    /// A constant (arity 0) is just `App(symbol, _, 0)` — there's no
    /// separate "Const" variant, constants are just applications with zero
    /// arguments.
    App(SymbolId, /* args_start */ u32, /* args_len */ u32),
}

/// The key actually used to look things up in the intern table.
///
/// This is a DIFFERENT type from `TermData` on purpose. `TermData::App`
/// stores a *location* in `args_pool` (`args_start`), but that location
/// doesn't exist yet the first time we're asking "has this term been built
/// before?" — we only know the *contents* of the args at that point
/// (`Vec<TermId>`), not where they'd live in the pool. So the intern table
/// is keyed on content (`InternKey`), while the actual stored data
/// (`TermData`) is keyed on location. Once a term is confirmed new, we copy
/// its args into `args_pool` and only THEN do we know the location to store
/// in `TermData::App`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum InternKey {
    Var(VarId),
    App(SymbolId, Vec<TermId>),
}

/// The arena: owns every term for one problem/session, and performs
/// hash-consing on every insertion.
#[derive(Debug, Default)]
pub struct TermArena {
    /// `terms[id]` = the `TermData` for `TermId == id`. This is the "source
    /// of truth" — `TermId` is literally just an index into this `Vec`.
    pub terms: Vec<TermData>,
    /// Flat, shared storage for every `App` term's argument list. Ranges
    /// into this are never reused/overwritten once written (append-only).
    pub args_pool: Vec<TermId>,
    /// The hash-consing table itself: structural content -> the `TermId`
    /// that was assigned to it the FIRST time it was built.
    intern_map: HashMap<InternKey, TermId>,
}

impl TermArena {
    pub fn new() -> Self {
        Self {
            terms: Vec::new(),
            args_pool: Vec::new(),
            intern_map: HashMap::new(),
        }
    }

    /// Number of DISTINCT terms stored (after interning collapses
    /// duplicates). If you build `f(a)` five times, this still only counts
    /// it once.
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// Build (or fetch the cached copy of) a variable term.
    ///
    /// **Algorithm:**
    /// 1. Build the lookup key `InternKey::Var(v)`.
    /// 2. Hash-map lookup in `intern_map`. If found -> return that existing
    ///    `TermId` immediately, nothing new is allocated.
    /// 3. If not found -> this is a genuinely new term: push `TermData::Var(v)`
    ///    onto `terms`, record the new `(key -> id)` mapping, return the id.
    ///
    /// **Complexity:** O(1) average (single `HashMap` lookup + optional insert).
    pub fn mk_var(&mut self, v: VarId) -> TermId {
        let key = InternKey::Var(v);
        if let Some(&id) = self.intern_map.get(&key) {
            return id;
        }
        let id = self.terms.len() as u32;
        self.terms.push(TermData::Var(v));
        self.intern_map.insert(key, id);
        id
    }

    /// Build (or fetch the cached copy of) an application term `symbol(args...)`.
    /// Pass `args = &[]` for a constant.
    ///
    /// **Algorithm:**
    /// 1. Build the lookup key `InternKey::App(symbol, args.to_vec())`.
    ///    NOTE: this clones `args` into an owned `Vec` just to check the
    ///    cache — see `// TODO(v0.3)` below, this is the known perf wart.
    /// 2. Hash-map lookup. Cache hit -> return existing `TermId`, done.
    /// 3. Cache miss -> this term is genuinely new:
    ///    a. Record where its args will live: `args_start = args_pool.len()`.
    ///    b. Append `args` onto the shared `args_pool` buffer.
    ///    c. Push `TermData::App(symbol, args_start, args.len())` onto `terms`.
    ///    d. Record the mapping in `intern_map`, return the new id.
    ///
    /// **Complexity:** O(k) where k = `args.len()`, dominated by the
    /// `args.to_vec()` clone for the lookup key and the `extend_from_slice`
    /// into `args_pool` on a cache miss. Both are linear in arity, which is
    /// normally small, so this is fine in practice for v0.1.
    ///
    /// // TODO(v0.3 — perf): `args.to_vec()` allocates a new `Vec` on EVERY
    /// call, even for cache hits (the common case once a problem has been
    /// running a while and most subterms already exist). Fix options, in
    /// order of how much they'd help:
    ///   1. Use `hashbrown`'s `raw_entry`/`raw_entry_mut` API to hash + look
    ///      up directly from `&[TermId]` without ever materializing an
    ///      owned `Vec` unless it turns out to be a genuine cache miss.
    ///   2. Or: keep a separate small "scratch" `Vec<TermId>` reused across
    ///      calls (avoid the *allocation*, even if we still technically
    ///      build a `Vec`-shaped key).
    /// This is exactly the kind of hot path that discrimination-tree
    /// indexing (also v0.3) will care about, so revisit both together.
    pub fn mk_app(&mut self, symbol: SymbolId, args: &[TermId]) -> TermId {
        let key = InternKey::App(symbol, args.to_vec());
        if let Some(&id) = self.intern_map.get(&key) {
            return id;
        }
        let args_start = self.args_pool.len() as u32;
        self.args_pool.extend_from_slice(args);
        let args_len = args.len() as u32;

        let id = self.terms.len() as u32;
        self.terms.push(TermData::App(symbol, args_start, args_len));
        self.intern_map.insert(key, id);
        id
    }

    /// Fetch the `TermData` for a `TermId`.
    ///
    /// **Algorithm:** direct index into `self.terms`. That's it — this is
    /// the entire reason `TermId` is a plain index instead of something
    /// fancier: lookup is a single array access, no hashing, no traversal.
    ///
    /// **Complexity:** O(1).
    ///
    /// # Panics
    /// Panics if `id` is out of bounds. This should never happen in
    /// practice UNLESS a `TermId` from a DIFFERENT `TermArena` gets passed
    /// in by mistake — `TermId`s are only valid within the arena that
    /// created them, there's no runtime tag proving which arena a given
    /// `TermId` "belongs" to.
    ///
    /// // TODO(v0.2 — safety/DX): consider a debug-only arena "generation"
    /// tag embedded alongside `TermId` (e.g. a wrapper struct that also
    /// carries an arena id, checked only in `debug_assertions`) so mixing
    /// up two arenas fails loudly instead of silently returning garbage
    /// data or panicking with a confusing out-of-bounds message.
    pub fn get(&self, id: TermId) -> TermData {
        self.terms[id as usize]
    }

    /// Fetch the argument list of a term as a slice. Empty for `Var` and
    /// for constants (`App` with zero args).
    ///
    /// **Algorithm:** read `(start, len)` out of `TermData::App`, slice
    /// directly into `args_pool`.
    ///
    /// **Complexity:** O(1) (slicing doesn't copy).
    pub fn args(&self, id: TermId) -> &[TermId] {
        match self.get(id) {
            TermData::App(_, start, len) => &self.args_pool[start as usize..(start + len) as usize],
            TermData::Var(_) => &[],
        }
    }

    pub fn is_var(&self, id: TermId) -> bool {
        matches!(self.get(id), TermData::Var(_))
    }

    pub fn is_app(&self, id: TermId) -> bool {
        matches!(self.get(id), TermData::App(..))
    }

    pub fn mk_const(&mut self, sym: SymbolId) -> TermId {
        self.mk_app(sym, &[])
    }

    /// The root symbol of an application term. `None` if `id` is a variable.
    ///
    /// **Complexity:** O(1).
    pub fn symbol_of(&self, id: TermId) -> Option<SymbolId> {
        match self.get(id) {
            TermData::App(s, _, _) => Some(s),
            TermData::Var(_) => None,
        }
    }

    /// Depth of a term. Variables AND constants (leaves — `App` with no
    /// args) are both depth 0; each level of application above that adds 1.
    /// e.g. `depth(a) = 0`, `depth(g(a)) = 1`, `depth(f(g(a), a)) = 2`.
    ///
    /// **Algorithm:** plain recursive tree walk (DFS). Base case: `Var` or
    /// argument-less `App` -> 0. Recursive case: 1 + the max depth among
    /// all direct children.
    ///
    /// **Complexity:** O(n) where n = number of nodes in the term (every
    /// node visited exactly once). Stack depth = depth of the term itself.
    ///
    /// // TODO(v0.3 — robustness): this recursion is not memoized and not
    /// tail-recursive. For pathologically deep terms (unlikely in normal
    /// FOL problems, but possible if e.g. Demodulation in v0.2 chains a lot
    /// of rewrites into one nested term) this could blow the stack. Low
    /// priority — revisit only if it actually bites during v0.2 equality
    /// reasoning testing.
    pub fn depth(&self, id: TermId) -> u32 {
        match self.get(id) {
            TermData::Var(_) => 0,
            TermData::App(_, start, len) => {
                let args = &self.args_pool[start as usize..(start + len) as usize];
                match
                    args
                        .iter()
                        .map(|&a| self.depth(a))
                        .max()
                {
                    Some(max_child_depth) => 1 + max_child_depth,
                    None => 0, // constant: no arguments, so no children to recurse into
                }
            }
        }
    }

    /// Total node count (symbol occurrences) in a term. Every `Var` or
    /// `App` node counts as 1, plus recursively all of its arguments.
    /// e.g. `size(a) = 1`, `size(f(a, a)) = 3` (f + a + a — note: even
    /// though both `a`s are the SAME `TermId` thanks to interning, `size`
    /// still counts each *occurrence*, not each distinct subterm).
    ///
    /// **Algorithm:** same shape as `depth` — recursive DFS, but summing
    /// instead of taking a max.
    ///
    /// **Complexity:** O(n), n = number of node occurrences reachable from
    /// `id` (NOT the number of distinct terms — a shared subterm used twice
    /// gets walked twice, since we're counting occurrences on purpose here).
    ///
    /// This is used by `Literal::weight()` / `Clause::weight` (see
    /// `clause.rs`) for the given-clause queue's weight heuristic, and is
    /// also earmarked as a raw input feature for `ClauseFeatures` once ML
    /// clause selection lands (v0.4 — see README §4.2).
    pub fn size(&self, id: TermId) -> u32 {
        match self.get(id) {
            TermData::Var(_) => 1,
            TermData::App(_, start, len) => {
                let args = &self.args_pool[start as usize..(start + len) as usize];
                1 +
                    args
                        .iter()
                        .map(|&a| self.size(a))
                        .sum::<u32>()
            }
        }
    }

    /// Render a term as a human-readable string like `f(a, X0)`, resolving
    /// symbol names through `symbols`. Mainly for debugging/tests, not
    /// meant to be a real proof-output serialization format.
    ///
    /// **Algorithm:** recursive DFS building up a `String`. Variables print
    /// as `X<id>` (raw numeric id, no attempt to recover original source
    /// names). Constants print as just the symbol name. Applications print
    /// as `name(arg1, arg2, ...)`.
    ///
    /// **Complexity:** O(n) tree walk, but note it allocates a `String` per
    /// recursive call (`args_str: Vec<String>` then `.join(", ")`) rather
    /// than writing into one shared buffer — so the actual allocation count
    /// is higher than the node count. Fine for debug output on small terms,
    /// not something you'd want in a hot path.
    ///
    /// // TODO(v0.2 — DX): once the parser assigns human-written variable
    /// names (`X`, `Y`, ...), consider threading a name-recovery map through
    /// here so debug output shows the ORIGINAL name instead of `X0`/`X1`.
    /// Right now this information is thrown away after parsing.
    ///
    /// // TODO(v0.3 — perf, only if this ever leaves "debug-only" territory):
    /// rewrite to take a `&mut impl std::fmt::Write` and recurse into that,
    /// instead of building and joining intermediate `Vec<String>`s.
    pub fn display(&self, id: TermId, symbols: &SymbolTable) -> String {
        match self.get(id) {
            TermData::Var(v) => format!("X{v}"),
            TermData::App(s, start, len) => {
                let name = symbols.name(s);
                if len == 0 {
                    name.to_string()
                } else {
                    let args = &self.args_pool[start as usize..(start + len) as usize];
                    let args_str: Vec<String> = args
                        .iter()
                        .map(|&a| self.display(a, symbols))
                        .collect();
                    format!("{name}({})", args_str.join(", "))
                }
            }
        }
    }
}

// TODO(v0.5 — parallelism): `TermArena` as written assumes single-threaded,
// exclusive `&mut` access. If/when the given-clause loop gets parallelized,
// concurrent interning (multiple threads racing to `mk_app` the same new
// term) becomes a real design question — this is a well-known contention
// point in production ATPs. Don't bolt on a `Mutex<TermArena>` naively
// without first checking whether that serializes the exact hot path
// parallelism was supposed to speed up; look at how Vampire/E-prover (or
// papers on parallel saturation) handle shared term banks before touching
// this.

/// Symbol table: maps names (`&str`) <-> `SymbolId`.
///
/// Kept SEPARATE from `TermArena` on purpose: symbol names are global to one
/// whole problem (predicate/function/constant names don't repeat per
/// clause), whereas `TermArena` is purely about term STRUCTURE and doesn't
/// need to know or care what anything is called. Mainly used by the parser
/// (to turn source text into `SymbolId`s) and by `display()` (to turn
/// `SymbolId`s back into readable text).
#[derive(Debug, Default)]
pub struct SymbolTable {
    /// `names[id]` = the string name for `SymbolId == id`.
    names: Vec<String>,
    /// Reverse lookup: name -> id, so `intern()` can dedupe.
    lookup: HashMap<String, SymbolId>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            names: Vec::new(),
            lookup: HashMap::new(),
        }
    }

    /// Get-or-create a `SymbolId` for a name.
    ///
    /// **Algorithm:** exactly the same hash-consing pattern as
    /// `TermArena::mk_var`/`mk_app` — check `lookup` first, return the
    /// existing id on a hit; on a miss, append to `names`, register in
    /// `lookup`, return the new id.
    ///
    /// **Complexity:** O(1) average on a hit. O(len(name)) on a miss (the
    /// `to_string()` clones + hashing the string), which only happens once
    /// per DISTINCT name ever seen.
    pub fn intern(&mut self, name: &str) -> SymbolId {
        if let Some(&id) = self.lookup.get(name) {
            return id;
        }
        let id = self.names.len() as u32;
        self.names.push(name.to_string());
        self.lookup.insert(name.to_string(), id);
        id
    }

    /// Reverse lookup: id -> name.
    ///
    /// **Complexity:** O(1), direct index into `names`.
    ///
    /// # Panics
    /// Panics if `id` was never returned by `intern()` on THIS table
    /// (same caveat as `TermArena::get` — no cross-table validity check).
    pub fn name(&self, id: SymbolId) -> &str {
        &self.names[id as usize]
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

// TODO(v0.2 — parser integration): `intern()` currently does `name.to_string()`
// TWICE on a cache miss (once for `names.push`, once for the `lookup.insert`
// key) — two allocations for one new symbol instead of one. Minor, but easy
// to fix by inserting first and cloning the stored `String` reference, or by
// switching `names: Vec<String>` + `lookup: HashMap<String, SymbolId>` to
// `names: Vec<Rc<str>>` + `lookup: HashMap<Rc<str>, SymbolId>` so the clone
// is a refcount bump instead of a fresh heap allocation.

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: setup symbol table with symbols frequently used in tests.
    struct Fixture {
        symbols: SymbolTable,
        f: u32, // f/2
        g: u32, // g/1
        a: u32, // a/0 (constant)
        b: u32, // b/0 (constant)
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
    fn variable_with_same_id_is_interned_to_same_term() {
        let mut arena = TermArena::new();
        let x1 = arena.mk_var(0);
        let x2 = arena.mk_var(0);
        let y = arena.mk_var(1);

        assert_eq!(x1, x2, "Var(0) created twice must get the same TermId");
        assert_ne!(x1, y, "Var(0) and Var(1) must have different TermIds");
        // Only 2 unique terms are actually stored (x1==x2 is counted once).
        assert_eq!(arena.len(), 2);
    }

    #[test]
    fn ground_constant_is_interned() {
        let fx = fixture();
        let mut arena = TermArena::new();

        let a1 = arena.mk_app(fx.a, &[]);
        let a2 = arena.mk_app(fx.a, &[]);
        let b1 = arena.mk_app(fx.b, &[]);

        assert_eq!(a1, a2, "constant `a` created twice must have the same TermId");
        assert_ne!(a1, b1, "constants `a` and `b` must be different");
        assert_eq!(arena.len(), 2); // a, b
    }

    #[test]
    fn identical_compound_terms_are_interned() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let b = arena.mk_app(fx.b, &[]);

        // f(a, b) constructed twice separately -> must get the same TermId.
        let t1 = arena.mk_app(fx.f, &[a, b]);
        let t2 = arena.mk_app(fx.f, &[a, b]);
        assert_eq!(t1, t2);

        // f(b, a) different argument order -> different term.
        let t3 = arena.mk_app(fx.f, &[b, a]);
        assert_ne!(t1, t3);

        // g(a) and f(a, b) obviously have different symbol/arity.
        let t4 = arena.mk_app(fx.g, &[a]);
        assert_ne!(t1, t4);
    }

    #[test]
    fn nested_terms_share_subterm_storage() {
        // f(g(a), g(a)) — subterm g(a) is used twice, must be shared
        // (not only same TermId, but indeed only 1 entry in the arena).
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);

        let ga_first = arena.mk_app(fx.g, &[a]);
        let ga_second = arena.mk_app(fx.g, &[a]);
        assert_eq!(ga_first, ga_second, "g(a) constructed twice must have the same TermId");

        let top = arena.mk_app(fx.f, &[ga_first, ga_second]);

        // Total unique terms: a, g(a), f(g(a), g(a)) = 3
        assert_eq!(arena.len(), 3);

        // args of `top` must both point to the same TermId (ga_first).
        let args = arena.args(top);
        assert_eq!(args, &[ga_first, ga_first]);
    }

    #[test]
    fn get_returns_correct_term_data() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let x = arena.mk_var(7);
        let a = arena.mk_app(fx.a, &[]);
        let fa = arena.mk_app(fx.f, &[a, x]);

        assert_eq!(arena.get(x), TermData::Var(7));
        assert!(arena.is_var(x));
        assert!(!arena.is_app(x));

        assert!(arena.is_app(a));
        assert_eq!(arena.symbol_of(a), Some(fx.a));
        assert_eq!(arena.args(a), &[] as &[u32]);

        assert_eq!(arena.symbol_of(fa), Some(fx.f));
        assert_eq!(arena.args(fa), &[a, x]);
    }

    #[test]
    fn depth_and_size_are_computed_correctly() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]); // depth 0, size 1
        let ga = arena.mk_app(fx.g, &[a]); // depth 1, size 2
        let fga_a = arena.mk_app(fx.f, &[ga, a]); // depth 2, size 4

        assert_eq!(arena.depth(a), 0);
        assert_eq!(arena.size(a), 1);

        assert_eq!(arena.depth(ga), 1);
        assert_eq!(arena.size(ga), 2);

        assert_eq!(arena.depth(fga_a), 2);
        assert_eq!(arena.size(fga_a), 4); // f, g, a, a
    }

    #[test]
    fn display_prints_readable_term() {
        let fx = fixture();
        let mut arena = TermArena::new();
        let a = arena.mk_app(fx.a, &[]);
        let x = arena.mk_var(0);
        let term = arena.mk_app(fx.f, &[a, x]);

        assert_eq!(arena.display(term, &fx.symbols), "f(a, X0)");
    }

    #[test]
    fn symbol_table_interns_names() {
        let mut symbols = SymbolTable::new();
        let f1 = symbols.intern("f");
        let f2 = symbols.intern("f");
        let g = symbols.intern("g");

        assert_eq!(f1, f2, "the same symbol name must get the same SymbolId");
        assert_ne!(f1, g);
        assert_eq!(symbols.name(f1), "f");
        assert_eq!(symbols.name(g), "g");
        assert_eq!(symbols.len(), 2);
    }

    #[test]
    fn arena_is_empty_initially() {
        let arena = TermArena::new();
        assert!(arena.is_empty());
        assert_eq!(arena.len(), 0);
    }
}
