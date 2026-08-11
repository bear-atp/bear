//! End-to-end example using the S-expression parser (instead of manually constructing
//! terms via the Rust API like `examples/socrates.rs`). Compare both to see the
//! difference: here, the problem is written in a separate text file
//! (`problems/socrates.sexp`), which is much more concise than calling
//! `arena.mk_var`/`arena.mk_app`/`Literal::positive` manually one by one.
//!
//! Run with: `cargo run --example socrates_sexpr`

use bear::saturation::{Saturation, SaturationResult};
use bear::term::SymbolTable;

fn main() {
    let input = std::fs::read_to_string("problems/socrates.sexp")
        .expect("failed to read problems/socrates.sexp (run from repo root)");

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
        println!(
            "  [{id}] {}",
            sat.clause_store().get(id).display(sat.arena(), &symbols)
        );
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
