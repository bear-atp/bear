//! End-to-end example using the S-expression parser (instead of manually constructing
//! terms via the Rust API like `examples/pelletier_barbara_chain_sexpr.rs`). Compare both to see the
//! difference: here, the problem is written in a separate text file
//! (`problems/pelletier_problem_43.sexp`), which is much more concise than calling
//! `arena.mk_var`/`arena.mk_app`/`Literal::positive` manually one by one.
//!
//! Run with: `cargo run --example pelletier_barbara_chain_sexpr`

use bear::saturation::{ Saturation, SaturationResult };
use bear::term::SymbolTable;

fn main() {
    let input = std::fs
        ::read_to_string("problems/pelletier_barbara_chain.sexp")
        .expect("failed to read problems/pelletier_barbara_chain.sexp (run from repo root)");

    let mut symbols = SymbolTable::new();
    let mut sat = Saturation::new();

    let ids = match sat.add_parsed_problem(&input, &mut symbols) {
        Ok(ids) => ids,
        Err(e) => {
            eprintln!("Parse error: {e}");
            std::process::exit(1);
        }
    };

    println!("Successfully parsed {} clauses:", ids.len());
    for &id in &ids {
        println!("  [{id}] {}", sat.clause_store().get(id).display(sat.arena(), &symbols));
    }

    println!("\nRunning given-clause loop...\n");

    match sat.run(10_000) {
        SaturationResult::Proved(id) => {
            println!("PROVED. Proof trace:");
            for clause_id in sat.proof_trace(id) {
                let clause = sat.clause_store().get(clause_id);
                println!(
                    "  [{clause_id}] {}   ({:?} <- {:?})",
                    clause.display(sat.arena(), &symbols),
                    clause.inference.rule,
                    clause.inference.parents
                );
            }
        }
        SaturationResult::Saturated => println!("SATURATED — no contradiction found."),
        SaturationResult::ClauseLimitReached => println!("Stopped: clause limit reached."),
    }
}

// Result
// Successfully parsed 4 clauses:
// [0] ~man(X0) | mortal(X0)
// [1] ~mortal(X0) | animal(X0)
// [2] man(socrates)
// [3] ~animal(socrates)

// Running given-clause loop...

// PROVED. Proof trace:
//  [3] ~animal(socrates)   (Input <- [])
//  [1] ~mortal(X0) | animal(X0)   (Input <- [])
//  [6] ~mortal(socrates)   (Resolution { left: 3, left_lit: 0, right: 1, right_lit: 1, unifier: Substitution { bindings: {6: 1} } } <- [3, 1])
//  [2] man(socrates)   (Input <- [])
//  [0] ~man(X0) | mortal(X0)   (Input <- [])
//  [5] mortal(socrates)   (Resolution { left: 2, left_lit: 0, right: 0, right_lit: 0, unifier: Substitution { bindings: {3: 1} } } <- [2, 0])
//  [11] ⊥   (Resolution { left: 6, left_lit: 0, right: 5, right_lit: 0, unifier: Substitution { bindings: {} } } <- [6, 5])
