//! Same Socrates syllogism as `examples/socrates_sexpr.rs`, but parsed from
//! TPTP CNF syntax instead of the S-expression format — demonstrates
//! `Saturation::add_parsed_tptp_problem` / `tptp::parse_tptp_problem`.
//!
//! Run with: `cargo run --example socrates_tptp`

use bear::saturation::{ Saturation, SaturationResult };
use bear::term::SymbolTable;

fn main() {
    let input = std::fs
        ::read_to_string("problems/socrates.tptp")
        .expect("failed to read problems/socrates.tptp (run from repo root)");

    let mut symbols = SymbolTable::new();
    let mut sat = Saturation::new();

    let ids = match sat.add_parsed_tptp_problem(&input, &mut symbols) {
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
// Successfully parsed 3 clauses:
//  [0] ~man(X0) | mortal(X0)
//  [1] man(socrates)
//  [2] ~mortal(socrates)
//
// Running given-clause loop...
//
// PROVED. Proof trace:
//  [1] man(socrates)   (Input <- [])
//  [0] ~man(X0) | mortal(X0)   (Input <- [])
//  [3] mortal(socrates)   (Resolution { left: 1, left_lit: 0, right: 0, right_lit: 0, unifier: Substitution { bindings: {1: 1} } } <- [1, 0])
//  [2] ~mortal(socrates)   (Input <- [])
//  [5] ⊥   (Resolution { left: 3, left_lit: 0, right: 2, right_lit: 0, unifier: Substitution { bindings: {} } } <- [3, 2])s
