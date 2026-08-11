//! End-to-end example: prove "Socrates is mortal" via refutation resolution.
//!
//! Run with: `cargo run --example socrates`
//!
//! Axioms (CNF):
//!   1. ~Man(X) | Mortal(X)     from "Man(x) -> Mortal(x)"
//!   2. Man(socrates)
//!   3. ~Mortal(socrates)      negated goal ("Socrates is NOT mortal")
//!
//! If the prover successfully derives an empty clause from these three, it means
//! the assumption "Socrates is not mortal" contradicts the axioms — thus proving
//! that Socrates is mortal.

use bear::clause::Literal;
use bear::saturation::{Saturation, SaturationResult};
use bear::term::SymbolTable;

fn main() {
    let mut symbols = SymbolTable::new();
    let man = symbols.intern("Man");
    let mortal = symbols.intern("Mortal");
    let socrates = symbols.intern("socrates");

    let mut sat = Saturation::new();
    let x = sat.arena_mut().mk_var(0);
    let socrates_term = sat.arena_mut().mk_app(socrates, &[]);

    println!("Axioms:");

    let c1 = sat.add_input_clause(vec![
        Literal::negative(man, vec![x]),
        Literal::positive(mortal, vec![x]),
    ]);
    println!(
        "  [{c1}] {}",
        sat.clause_store().get(c1).display(sat.arena(), &symbols)
    );

    let c2 = sat.add_input_clause(vec![Literal::positive(man, vec![socrates_term])]);
    println!(
        "  [{c2}] {}",
        sat.clause_store().get(c2).display(sat.arena(), &symbols)
    );

    let c3 = sat.add_input_clause(vec![Literal::negative(mortal, vec![socrates_term])]);
    println!(
        "  [{c3}] {} (negated goal)",
        sat.clause_store().get(c3).display(sat.arena(), &symbols)
    );

    println!("\nRunning given-clause loop...\n");

    match sat.run(10_000) {
        SaturationResult::Proved(id) => {
            println!("PROVED. Proof trace:");
            for clause_id in sat.proof_trace(id) {
                let clause = sat.clause_store().get(clause_id);
                let rule = format!("{:?}", clause.inference.rule);
                let parents = if clause.inference.parents.is_empty() {
                    String::new()
                } else {
                    format!(
                        " <- {}",
                        clause
                            .inference
                            .parents
                            .iter()
                            .map(|p| p.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                println!(
                    "  [{clause_id}] {}   ({rule}{parents})",
                    clause.display(sat.arena(), &symbols)
                );
            }
            println!("\n=> Socrates is proven to be mortal. QED.");
        }
        SaturationResult::Saturated => {
            println!("SATURATED — no contradiction found (should not happen in this example).");
        }
        SaturationResult::ClauseLimitReached => {
            println!("Berhenti: clause limit reached before finding proof.");
        }
    }
}
