//! End-to-end example using the S-expression parser (instead of manually constructing
//! terms via the Rust API like `examples/pelletier_problem_43_sexpr.rs`). Compare both to see the
//! difference: here, the problem is written in a separate text file
//! (`problems/pelletier_problem_43.sexp`), which is much more concise than calling
//! `arena.mk_var`/`arena.mk_app`/`Literal::positive` manually one by one.
//!
//! Run with: `cargo run --example pelletier_problem_43_sexpr`

use bear::saturation::{ Saturation, SaturationResult };
use bear::term::SymbolTable;

fn main() {
    let input = std::fs
        ::read_to_string("problems/pelletier_problem_43.sexp")
        .expect("failed to read problems/pelletier_problem_43.sexp (run from repo root)");

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

    // When max_clauses set to 10.000 we got a timeout
    // 200_000 still timeout
    match sat.run(200_000) {
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
// Successfully parsed 8 clauses:
//  [0] ~q(X0, X1) | ~p(X2, X0) | p(X2, X1)
//  [1] ~q(X0, X1) | ~p(X2, X1) | p(X2, X0)
//  [2] q(X0, X1) | p(f(X0, X1), X0) | p(f(X0, X1), X1)
//  [3] q(X0, X1) | ~p(f(X0, X1), X1) | ~p(f(X0, X1), X0)
//  [4] q(a, b)
//  [5] ~q(b, a) | q(b, c)
//  [6] ~q(b, a) | q(a, c)
//  [7] ~q(b, a) | ~q(b, a)
//
// Running given-clause loop...
//
// Stopped: clause limit reached.