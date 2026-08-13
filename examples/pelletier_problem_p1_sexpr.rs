//! End-to-end example using the S-expression parser (instead of manually constructing
//! terms via the Rust API like `examples/pelletier_problem_p1_sexpr.rs`). Compare both to see the
//! difference: here, the problem is written in a separate text file
//! (`problems/pelletier_problem_43.sexp`), which is much more concise than calling
//! `arena.mk_var`/`arena.mk_app`/`Literal::positive` manually one by one.
//!
//! Run with: `cargo run --example pelletier_problem_p1_sexpr`

use bear::saturation::{ Saturation, SaturationResult };
use bear::term::SymbolTable;

fn main() {
    let input = std::fs
        ::read_to_string("problems/sexp/pelletier_problem_p1.sexp")
        .expect("failed to read problems/sexp/pelletier_problem_p1.sexp (run from repo root)");

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
//  [0] ~p | q
//  [1] ~q | r
//  [2] p
//  [3] ~r
//
// Running given-clause loop...
//
// PROVED. Proof trace:
//  [3] ~r   (Input <- [])
//  [1] ~q | r   (Input <- [])
//  [6] ~q   (Resolution { left: 3, left_lit: 0, right: 1, right_lit: 1, unifier: Substitution { bindings: {} } } <- [3, 1])
//  [2] p   (Input <- [])
//  [0] ~p | q   (Input <- [])
//  [5] q   (Resolution { left: 2, left_lit: 0, right: 0, right_lit: 0, unifier: Substitution { bindings: {} } } <- [2, 0])
//  [11] ⊥   (Resolution { left: 6, left_lit: 0, right: 5, right_lit: 0, unifier: Substitution { bindings: {} } } <- [6, 5])
