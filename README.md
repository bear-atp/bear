# bear

Bear is an attempt at building an ATP (Automated Theorem Prover) in pure Rust, loosely inspired by [Vampire](https://vprover.github.io/)'s architecture — a saturation-based prover using resolution and (eventually) superposition calculus.

> **Status: v0.1 MVP complete.** Bear can prove first-order problems that don't require equality reasoning, using Resolution + Factoring over a naive given-clause loop. 73 tests passing, zero warnings.

This is a learning/research project, not a competitive theorem prover. The goal is to understand automated reasoning deeply by building the real thing from scratch — term representation, unification, inference rules, saturation, and eventually equality reasoning and ML-guided search — rather than to compete with Vampire, E, or Zipperposition on CASC benchmarks.

---

## What Bear can do right now (v0.1)

- Parse first-order clause sets from a simple **S-expression format** (Prolog/TPTP-style variable convention: uppercase = variable, lowercase = constant/function/predicate)
- Represent terms with **hash-consing (interning)** — structurally identical terms always share the same `TermId`, giving `O(1)` equality and automatic subterm sharing
- **Unify** terms and literals (Robinson-style, with occurs-check on by default)
- Perform **Resolution** and **Factoring** inference, correctly handling variable scope via rename-apart
- Run a **given-clause saturation loop** (FIFO, active/passive clause sets) that finds refutations automatically, including multi-step proofs
- Reconstruct a **proof trace** (which clauses were derived from which, via which rule) after a proof is found
- Report three outcomes: `Proved`, `Saturated` (no contradiction found), or `ClauseLimitReached` (a simple stand-in for a timeout)

### Example

```lisp
; problems/socrates.sexp
(clause (not (man X)) (mortal X))   ; man(x) -> mortal(x)
(clause (man socrates))
(clause (not (mortal socrates)))    ; negated goal
```

```
$ cargo run --example socrates_sexpr

Berhasil parse 3 clause:
  [0] ~man(X0) | mortal(X0)
  [1] man(socrates)
  [2] ~mortal(socrates)

PROVED. Proof trace:
  [1] man(socrates)          (Input <- [])
  [0] ~man(X0) | mortal(X0)  (Input <- [])
  [3] mortal(socrates)       (Resolution <- [1, 0])
  [2] ~mortal(socrates)      (Input <- [])
  [5] ⊥                      (Resolution <- [3, 2])
```

---

## Architecture

```
term        Term representation + hash-consing (TermArena, SymbolTable)
   ↓
clause      Literal, Clause, ClauseStore, InferenceInfo (proof provenance)
   ↓
unify       Substitution + Robinson unification, unify_literals
   ↓
inference   VarGen + rename_apart, Resolution, Factoring
   ↓
saturation  Given-clause loop (active/passive sets, FIFO)
   ↓
parser      S-expression → Vec<Literal> (feeds directly into saturation)
```

Each layer only depends on the ones above it (`term` has zero dependencies; `saturation` depends on everything). No circular dependencies between modules.

### Key design decisions

| Decision | Rationale |
|---|---|
| Terms stored in an arena, addressed by `u32` index | Cheap to copy/hash/compare, no lifetime fights, no `Rc` overhead |
| Structural interning (hash-consing) | Equal terms always get the same `TermId`; subterms are automatically shared in memory |
| `VarId` scoped per-clause, not globally | Matches how clauses are naturally written/parsed; cross-clause safety is handled explicitly by `rename_apart` before Resolution |
| Every `Clause` carries `InferenceInfo` (rule + parents) from day one | Proof reconstruction works without any retrofit — you can always walk backward from `⊥` to the input axioms |
| `resolve()` returns *all* valid resolvent pairs, not just the first | This is what a real saturation loop needs — it can't stop at the first match |
| Empty-clause detection happens immediately at derivation time | No need to wait for the clause to cycle through the passive queue |

---

## Limitations (read this before relying on Bear for anything)

Bear is deliberately **correctness-first, MVP-scoped**. A lot is missing on purpose — this is the honest list:

- **No equality reasoning.** No `=`, no Superposition, no Demodulation, no Equality Resolution/Factoring. Any problem that needs equational reasoning (groups, rings, most interesting math) cannot be proved yet. This is the headline feature of v0.2.
- **No term ordering (KBO/LPO).** Without an ordering, there's no principled way to restrict rewriting direction or do literal selection — both needed before Superposition can be sound and terminating.
- **No indexing.** Given-clause vs. active-clause matching is brute-force `O(n)` per step, checking every literal pair. This will not scale past small/toy problems. Real provers use discrimination trees or substitution trees (planned for v0.3).
- **No simplification or redundancy elimination.** No subsumption, no tautology deletion, no forward/backward simplification. The clause store accumulates a lot of dead-end clauses (you can see this directly in a proof trace — clause IDs that were generated but never used).
- **FIFO given-clause selection only.** No age-weight ratio, no multiple priority queues. Every clause is processed strictly in the order it was derived, which is a poor heuristic for anything but small problems.
- **`ClauseLimitReached` is not a real timeout.** It's a clause-count cutoff, not wall-clock based. There's currently no way to bound proof search by actual time.
- **The parser is not TPTP.** It's a custom S-expression format designed to *look like* TPTP conventions (variable casing) as a stepping stone, but it cannot read real TPTP problem files from the standard library yet.
- **Substitution is a plain `HashMap`, not union-find.** Chasing variable binding chains is `O(chain length)` per lookup; no path compression yet.
- **Clauses are `.clone()`d during the given-clause loop** to work around borrow-checker constraints between `ClauseStore` and `TermArena`. Functionally correct, but a real perf cost once clauses get large.
- **No parallelism.** Single-threaded throughout.
- **No machine learning integration yet.** The `ClauseSelector` trait / `ClauseFeatures` extraction / training-data logging described in the roadmap don't exist in code yet — v0.1 only has the naive heuristic-free FIFO queue.
- **No CLI / no way to run arbitrary `.sexp` files from the command line.** Right now you drive Bear through the library API or hand-written `examples/*.rs` files; there's no `bear prove problem.sexp` binary yet.
- **Not benchmarked against anything.** No TPTP library run, no comparison numbers vs. any other prover. "It proves Socrates is mortal" is currently the extent of validation — more Pelletier/TPTP-style problems are needed before trusting Bear on anything nontrivial.

If any of these matter for what you're trying to do today, Bear probably isn't ready for it yet — check the roadmap below for what's next.

---

## Roadmap

### ✅ v0.1 — MVP (done)

Propositional + first-order resolution that actually works, with a text-based input format.

- [x] `TermArena` with hash-consing
- [x] `Literal` / `Clause` representation
- [x] Robinson unification (occurs-check on by default, togglable)
- [x] Substitution + variable rename-apart
- [x] Resolution + Factoring inference rules
- [x] Naive FIFO given-clause loop
- [x] Empty-clause detection = proof found
- [x] Simple S-expression input format
- [x] `Proved` / `Saturated` / `ClauseLimitReached` output
- [x] Proof trace reconstruction
- [x] Tests covering classic non-equality problems (syllogisms, multi-step chains)

### v0.2 — Equality & Ordering

Turning this into an actual superposition prover.

- [ ] Term ordering: **KBO** (Knuth-Bendix Ordering)
- [ ] **Superposition** (left & right), **Equality Resolution**, **Equality Factoring**
- [ ] **Demodulation**, **tautology deletion**, **forward/backward subsumption**
- [ ] Given-clause queue upgrade: age-weight ratio (replacing plain FIFO)
- [ ] Real **TPTP parser** (FOF/CNF) — unlocks the standard problem library for benchmarking
- [ ] Cleaner proof output format

### v0.3 — Performance

Making it not fall over on anything past toy problems.

- [ ] **Discrimination tree** indexing for unification/matching queries
- [ ] Union-find-based substitution (replace `HashMap` chasing)
- [ ] Multiple passive queues with different strategies
- [ ] Literal selection strategies
- [ ] Benchmarks against a TPTP subset

### v0.4 — Machine Learning

Learned given-clause selection instead of hand-tuned heuristics.

- [ ] `ClauseFeatures` extraction (symbol counts, depth, goal-similarity, etc.)
- [ ] Pluggable `ClauseSelector` trait (heuristic vs. learned, swappable)
- [ ] Proof-search logging for training data
- [ ] First model: gradient-boosted tree scoring given-clauses (`linfa`), evaluated against the FIFO/age-weight baseline

### v0.5+ — Further experiments (research territory, no promises)

- [ ] Premise selection
- [ ] Neural clause scoring via ONNX (`ort`)
- [ ] RL-based given-clause selection
- [ ] Parallel saturation

---

## Getting started

```bash
# Run the full test suite
cargo test
```

# Run the end-to-end demo (manual clause construction via the Rust API)

```bash
cargo run --example socrates
```

# Run the same proof, but driven from a text file via the parser

```bash
cargo run --example socrates_sexpr
```

Writing your own problem: create a `.sexp` file with one or more `(clause ...)` forms (see `problems/socrates.sexp` for a full example), then feed it to `Saturation::add_parsed_problem`.

## References

- Kovács, L. & Voronkov, A. — *First-Order Theorem Proving and Vampire*
- Bachmair, L. & Ganzinger, H. — Resolution & Superposition chapter, *Handbook of Automated Reasoning*
- Baader, F. & Nipkow, T. — *Term Rewriting and All That*
- [TPTP Problem Library](https://www.tptp.org/)
- ENIGMA (E-prover + learned clause selection), Deepire (Vampire fork with ML-guided given-clause selection) — reference points for the v0.4+ ML roadmap