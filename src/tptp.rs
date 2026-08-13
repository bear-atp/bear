//! TPTP CNF input format parser (the `cnf(name, role, formula).` dialect —
//! see http://www.tptp.org/). This is deliberately CNF-only: `parser.rs`'s
//! module doc already flagged that a full TPTP parser (FOF, with explicit
//! quantifiers/connectives that need Skolemization + CNF conversion before
//! they mean anything to a resolution engine) is a separate, much bigger
//! project. This module covers the subset that maps directly onto
//! `Vec<Literal>` with no conversion step, same as `parser.rs` does for its
//! own S-expression format.
//!
//! # Syntax
//!
//! ```text
//! % comments start with a percent sign and run to end of line
//! cnf(ax1, axiom, ~man(X) | mortal(X)).
//! cnf(ax2, axiom, man(socrates)).
//! cnf(goal, negated_conjecture, ~mortal(socrates)).
//! ```
//!
//! - **Statement**: `cnf(<name>, <role>, <formula>).` — the trailing `.` is
//!   required. `<name>` and `<role>` are parsed but otherwise ignored (Bear
//!   has no concept yet of "this clause is the goal" — same gap flagged in
//!   `parser.rs`'s TODO).
//! - **Formula**: a single literal, or a `|`-separated disjunction of
//!   literals, optionally wrapped in parens (`(l1 | l2 | ...)` or bare
//!   `l1 | l2`).
//! - **Literal**: `pred(arg...)` for positive, `~pred(arg...)` for negative.
//!   A propositional predicate (arity 0) may be written without parens,
//!   e.g. `p` or `~p`.
//! - **Term**: `name` (a variable if it starts with an uppercase letter or
//!   `_`, a constant otherwise — standard TPTP convention) or `f(arg...)`
//!   for function application.
//! - **Variables are scoped per-clause**, same as `parser.rs`.
//! - Equality literals (`t1 = t2`, `t1 != t2`) are NOT supported — Bear has
//!   no paramodulation yet, so accepting them would silently produce a
//!   clause set no proof search could ever use correctly. Parsing one is a
//!   hard error with a message saying so, rather than a wrong answer.

use std::collections::HashMap;

use crate::clause::Literal;
use crate::parser::ParseError;
use crate::term::{ SymbolTable, TermArena, TermId, VarId };

// ---------------------------------------------------------------------
// Tokenizer
// ---------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum Token {
    LParen,
    RParen,
    Comma,
    Dot,
    Pipe,
    Tilde,
    Equals,
    NotEquals,
    Ident(String),
}

/// Turn raw TPTP source text into a flat token stream, each tagged with the
/// (1-indexed) line it started on.
///
/// **Algorithm:** single left-to-right scan, mirroring `parser::tokenize`'s
/// structure but with TPTP's punctuation set (`( ) , . | ~ = !=`) and two
/// comment styles (`%` to end of line, `/* ... */` block comments — TPTP
/// supports both).
///
/// **Complexity:** O(n) in input length.
fn tokenize(input: &str) -> Result<Vec<(Token, usize)>, ParseError> {
    let mut tokens = Vec::new();
    let mut line = 1usize;
    let mut chars = input.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\r' => {
                chars.next();
            }
            '\n' => {
                chars.next();
                line += 1;
            }
            '%' => {
                while let Some(&c2) = chars.peek() {
                    if c2 == '\n' {
                        break;
                    }
                    chars.next();
                }
            }
            '/' => {
                let start_line = line;
                chars.next();
                if chars.peek() == Some(&'*') {
                    chars.next();
                    loop {
                        match chars.next() {
                            Some('*') if chars.peek() == Some(&'/') => {
                                chars.next();
                                break;
                            }
                            Some('\n') => {
                                line += 1;
                            }
                            Some(_) => {}
                            None => {
                                return Err(ParseError {
                                    line: start_line,
                                    message: "block comment '/*' doesn't close with '*/'".to_string(),
                                });
                            }
                        }
                    }
                } else {
                    return Err(ParseError {
                        line: start_line,
                        message: "'/' unexpected out of scope".to_string(),
                    });
                }
            }
            '(' => {
                chars.next();
                tokens.push((Token::LParen, line));
            }
            ')' => {
                chars.next();
                tokens.push((Token::RParen, line));
            }
            ',' => {
                chars.next();
                tokens.push((Token::Comma, line));
            }
            '.' => {
                chars.next();
                tokens.push((Token::Dot, line));
            }
            '|' => {
                chars.next();
                tokens.push((Token::Pipe, line));
            }
            '~' => {
                chars.next();
                tokens.push((Token::Tilde, line));
            }
            '=' => {
                chars.next();
                tokens.push((Token::Equals, line));
            }
            '!' => {
                let start_line = line;
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    tokens.push((Token::NotEquals, line));
                } else {
                    return Err(ParseError {
                        line: start_line,
                        message: "'!' unexpected (only known part of '!=')".to_string(),
                    });
                }
            }
            '\'' => {
                // Single-quoted atom, e.g. 'my atom name' — content taken
                // verbatim between the quotes as the identifier text.
                let start_line = line;
                chars.next();
                let mut sym = String::new();

                loop {
                    match chars.next() {
                        Some('\'') => {
                            break;
                        }
                        Some('\n') => {
                            return Err(ParseError {
                                line: start_line,
                                message: "tanda kutip tunggal tidak ditutup sebelum akhir baris".to_string(),
                            });
                        }
                        Some(c2) => sym.push(c2),
                        None => {
                            return Err(ParseError {
                                line: start_line,
                                message: "tanda kutip tunggal tidak ditutup sebelum EOF".to_string(),
                            });
                        }
                    }
                }
                tokens.push((Token::Ident(sym), start_line));
            }
            _ => {
                let start_line = line;
                let mut sym = String::new();
                while let Some(&c2) = chars.peek() {
                    if
                        c2.is_whitespace() ||
                        matches!(c2, '(' | ')' | ',' | '.' | '|' | '~' | '=' | '!' | '\'' | '%')
                    {
                        break;
                    }
                    sym.push(c2);
                    chars.next();
                }

                if sym.is_empty() {
                    // Shouldn't happen given the branches above, but guard
                    // againts an infinite loop on an unrecognized character
                    return Err(ParseError {
                        line: start_line,
                        message: format!("karakter tidak dikenal: '{c}'"),
                    });
                }
                tokens.push((Token::Ident(sym), start_line));
            }
        }
    }

    Ok(tokens)
}

// ---------------------------------------------------------------------
// Semantic pass: tokens -> Literal/Clause
// ---------------------------------------------------------------------

/// Same variable-vs-constant rule as `parser.rs`: uppercase-or-`_` first
/// character means variable, everything else is a constant/function/
/// predicate name.
fn is_variable_name(s: &str) -> bool {
    s.chars()
        .next()
        .map(|c| (c.is_uppercase() || c == '_'))
        .unwrap_or(false)
}

/// Per-clause parsing context — mirrors `parser::ClauseCtx`. A fresh one is
/// built per `cnf(...)` statement so variable numbering restarts at 0 for
/// each clause (matching `VarId`'s per-clause scoping).
struct Parser<'a> {
    tokens: &'a [(Token, usize)],
    pos: usize,
    arena: &'a mut TermArena,
    symbols: &'a mut SymbolTable,
    var_map: HashMap<String, VarId>,
    next_var: VarId,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(t, _)| t)
    }

    fn peek_line(&self) -> usize {
        self.tokens
            .get(self.pos)
            .map(|(_, l)| *l)
            .unwrap_or_else(|| {
                self.tokens
                    .last()
                    .map(|(_, l)| *l)
                    .unwrap_or(0)
            })
    }

    fn advance(&mut self) -> Option<Token> {
        let t = self.tokens.get(self.pos).map(|(t, _)| t.clone());
        if t.is_some() {
            self.pos += 1;
        }

        t
    }

    fn expect(&mut self, expected: &Token, what: &str) -> Result<(), ParseError> {
        match self.advance() {
            Some(ref t) if t == expected => Ok(()),
            Some(other) =>
                Err(ParseError {
                    line: self.tokens[self.pos - 1].1,
                    message: format!("diharapkan {what}, ditemukan {other:?}"),
                }),
            None =>
                Err(ParseError {
                    line: self.peek_line(),
                    message: format!("diharapkan {what}, tapi EOF"),
                }),
        }
    }

    fn expect_ident(&mut self, what: &str) -> Result<String, ParseError> {
        match self.advance() {
            Some(Token::Ident(s)) => Ok(s),
            Some(other) =>
                Err(ParseError {
                    line: self.tokens[self.pos - 1].1,
                    message: format!("diharapkan {what}, ditemukan {other:?}"),
                }),
            None =>
                Err(ParseError {
                    line: self.peek_line(),
                    message: format!("diharapkan {what}, tapi EOF"),
                }),
        }
    }

    fn var_id(&mut self, name: &str) -> VarId {
        if let Some(&id) = self.var_map.get(name) {
            return id;
        }
        let id = self.next_var;
        self.next_var += 1;
        self.var_map.insert(name.to_string(), id);
        id
    }

    /// Parse one TERM: a variable, a constant, or `name(arg, ...)`.
    fn parse_term(&mut self) -> Result<TermId, ParseError> {
        let line = self.peek_line();
        let name = self.expect_ident("nama term")?;
        if is_variable_name(&name) {
            let id = self.var_id(&name);
            return Ok(self.arena.mk_var(id));
        }
        if self.peek() == Some(&Token::LParen) {
            self.advance();
            let mut args = Vec::new();
            args.push(self.parse_term()?);
            while self.peek() == Some(&Token::Comma) {
                self.advance();
                args.push(self.parse_term()?);
            }
            self.expect(&Token::RParen, "')' penutup argumen term")?;
            let sym = self.symbols.intern(&name);
            Ok(self.arena.mk_app(sym, &args))
        } else {
            let _ = line;
            let sym = self.symbols.intern(&name);
            Ok(self.arena.mk_app(sym, &[]))
        }
    }

    /// Parse one LITERAL: optional leading `~`, then `pred(arg...)` or bare
    /// `pred`. Equality (`=`/`!=`) between two terms is rejected explicitly
    /// with a clear "not supported" error rather than silently mis-parsed.
    fn parse_literal(&mut self) -> Result<Literal, ParseError> {
        let negated = if self.peek() == Some(&Token::Tilde) {
            self.advance();
            true
        } else {
            false
        };

        let line = self.peek_line();
        let name = self.expect_ident("nama predicate")?;
        if is_variable_name(&name) {
            return Err(ParseError {
                line,
                message: format!(
                    "'{name}' diawali huruf besar (dianggap variable), tidak bisa dipakai sebagai nama predicate"
                ),
            });
        }

        let args = if self.peek() == Some(&Token::LParen) {
            self.advance();
            let mut args = Vec::new();
            args.push(self.parse_term()?);
            while self.peek() == Some(&Token::Comma) {
                self.advance();
                args.push(self.parse_term()?);
            }
            self.expect(&Token::RParen, "')' penutup argumen predicate")?;
            args
        } else {
            Vec::new()
        };

        if matches!(self.peek(), Some(Token::Equals) | Some(Token::NotEquals)) {
            return Err(ParseError {
                line: self.peek_line(),
                message: "literal equality ('=' / '!=') belum didukung — Bear belum punya paramodulation".to_string(),
            });
        }

        let pred = self.symbols.intern(&name);
        if negated {
            Ok(Literal::negative(pred, args))
        } else {
            Ok(Literal::positive(pred, args))
        }
    }

    /// Parse a CNF formula: a bare literal, a `|`-separated disjunction, or
    /// either wrapped in one layer of parens.
    fn parse_cnf_formula(&mut self) -> Result<Vec<Literal>, ParseError> {
        let parenthesized = self.peek() == Some(&Token::LParen);
        if parenthesized {
            self.advance();
        }

        let mut literals = vec![self.parse_literal()?];
        while self.peek() == Some(&Token::Pipe) {
            self.advance();
            literals.push(self.parse_literal()?);
        }

        if parenthesized {
            self.expect(&Token::RParen, "')' penutup formula")?;
        }
        Ok(literals)
    }

    /// Parse one `cnf(name, role, formula).` statement.
    fn parse_cnf_statement(&mut self) -> Result<Vec<Literal>, ParseError> {
        let line = self.peek_line();
        let keyword = self.expect_ident("'cnf'")?;
        if keyword != "cnf" {
            return Err(ParseError {
                line,
                message: format!("diharapkan 'cnf(...)', ditemukan '{keyword}(...)'"),
            });
        }
        self.expect(&Token::LParen, "'(' setelah 'cnf'")?;
        self.expect_ident("nama clause")?;
        self.expect(&Token::Comma, "',' setelah nama clause")?;
        self.expect_ident("role (mis. 'axiom', 'conjecture')")?;
        self.expect(&Token::Comma, "',' setelah role")?;
        let literals = self.parse_cnf_formula()?;
        self.expect(&Token::RParen, "')' penutup 'cnf(...)'")?;
        self.expect(&Token::Dot, "'.' penutup statement")?;
        Ok(literals)
    }
}

/// Parse an entire TPTP CNF problem (a sequence of `cnf(...).` statements)
/// into a list of clauses, each as `Vec<Literal>`. Terms are built directly
/// into `arena`, predicate/function/constant names are interned into
/// `symbols` — both owned by the caller, same contract as
/// `parser::parse_problem`.
///
/// **Algorithm:** tokenize the whole input once, then repeatedly parse one
/// `cnf(...).` statement at a time (each gets its own fresh variable scope)
/// until the token stream is exhausted.
///
/// **Complexity:** O(n) in input length for tokenizing, plus O(total term
/// size across the whole problem) for the semantic pass.
pub fn parse_tptp_problem(
    input: &str,
    arena: &mut TermArena,
    symbols: &mut SymbolTable
) -> Result<Vec<Vec<Literal>>, ParseError> {
    let tokens = tokenize(input)?;
    let mut clauses = Vec::new();
    let mut pos = 0usize;

    while pos < tokens.len() {
        let mut parser = Parser {
            tokens: &tokens,
            pos,
            arena,
            symbols,
            var_map: HashMap::new(),
            next_var: 0,
        };
        let literals = parser.parse_cnf_statement()?;
        pos = parser.pos;
        clauses.push(literals);
    }

    Ok(clauses)
}

#[cfg(test)]
mod tests {
    use crate::clause::InferenceRule;
    use crate::saturation::{ Saturation, SaturationResult };
    use crate::term::SymbolTable;

    #[test]
    fn parses_single_ground_positive_literal() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::tptp
            ::parse_tptp_problem("cnf(a1, axiom, man(socrates)).", &mut arena, &mut symbols)
            .unwrap();

        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].len(), 1);
        assert!(clauses[0][0].is_positive());
        assert_eq!(clauses[0][0].display(&arena, &symbols), "man(socrates)");
    }

    #[test]
    fn parses_negated_literal_via_tilde() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::tptp
            ::parse_tptp_problem(
                "cnf(neg, negated_conjecture, ~mortal(socrates)).",
                &mut arena,
                &mut symbols
            )
            .unwrap();

        assert!(clauses[0][0].is_negative());
        assert_eq!(clauses[0][0].display(&arena, &symbols), "~mortal(socrates)");
    }

    #[test]
    fn parses_disjunction_with_parens() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::tptp
            ::parse_tptp_problem(
                "cnf(ax1, axiom, ( ~man(X) | mortal(X) )).",
                &mut arena,
                &mut symbols
            )
            .unwrap();

        let clause = &clauses[0];
        assert_eq!(clause.len(), 2);
        assert_eq!(clause[0].display(&arena, &symbols), "~man(X0)");
        assert_eq!(clause[1].display(&arena, &symbols), "mortal(X0)");
    }

    #[test]
    fn parses_disjunction_without_parens() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::tptp
            ::parse_tptp_problem("cnf(ax1, axiom, ~man(X) | mortal(X)).", &mut arena, &mut symbols)
            .unwrap();
        assert_eq!(clauses[0].len(), 2);
    }

    #[test]
    fn parses_propositional_literal_without_parens() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::tptp
            ::parse_tptp_problem("cnf(c1, axiom, p | ~q).", &mut arena, &mut symbols)
            .unwrap();
        assert_eq!(clauses[0][0].display(&arena, &symbols), "p");
        assert_eq!(clauses[0][1].display(&arena, &symbols), "~q");
    }

    #[test]
    fn parses_nested_function_application() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::tptp
            ::parse_tptp_problem("cnf(c1, axiom, p(f(X, a))).", &mut arena, &mut symbols)
            .unwrap();
        assert_eq!(clauses[0][0].display(&arena, &symbols), "p(f(X0, a))");
    }

    #[test]
    fn comments_are_ignored_both_styles() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let input =
            "
        % full-line comment
        /* block
           comment */
        cnf(c1, axiom, man(socrates)). % trailing comment
        ";
        let clauses = crate::tptp::parse_tptp_problem(input, &mut arena, &mut symbols).unwrap();
        assert_eq!(clauses.len(), 1);
    }

    #[test]
    fn multiple_statements_parsed_in_order() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let input = "cnf(c1, axiom, p(a)).\ncnf(c2, axiom, q(b)).\ncnf(c3, axiom, r(c)).";
        let clauses = crate::tptp::parse_tptp_problem(input, &mut arena, &mut symbols).unwrap();
        assert_eq!(clauses.len(), 3);
    }

    #[test]
    fn variable_scope_is_independent_across_clauses() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let input = "cnf(c1, axiom, p(X)).\ncnf(c2, axiom, q(X)).";
        let clauses = crate::tptp::parse_tptp_problem(input, &mut arena, &mut symbols).unwrap();
        assert!(matches!(arena.get(clauses[0][0].args[0]), crate::term::TermData::Var(_)));
        assert!(matches!(arena.get(clauses[1][0].args[0]), crate::term::TermData::Var(_)));
    }

    #[test]
    fn error_on_equality_literal() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let err = crate::tptp
            ::parse_tptp_problem("cnf(c1, axiom, a = b).", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("equality") || err.message.contains("paramodulation"));
    }

    #[test]
    fn error_on_missing_trailing_dot() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let err = crate::tptp
            ::parse_tptp_problem("cnf(c1, axiom, p(a))", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("'.'"));
    }

    #[test]
    fn error_on_variable_used_as_predicate_name() {
        let mut arena = crate::term::TermArena::new();
        let mut symbols = SymbolTable::new();
        let err = crate::tptp
            ::parse_tptp_problem("cnf(c1, axiom, X(a)).", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("variable"));
    }

    #[test]
    fn parsed_problem_can_be_proved_end_to_end() {
        let mut symbols = SymbolTable::new();
        let mut sat = Saturation::new();

        let input =
            "
        cnf(ax1, axiom, ~man(X) | mortal(X)).
        cnf(ax2, axiom, man(socrates)).
        cnf(goal, negated_conjecture, ~mortal(socrates)).
        ";
        let ids = sat.add_parsed_tptp_problem(input, &mut symbols).unwrap();
        assert_eq!(ids.len(), 3);

        let result = sat.run(1000);
        match result {
            SaturationResult::Proved(id) => {
                let trace = sat.proof_trace(id);
                assert!(trace.len() >= 4);
                for input_id in &ids {
                    assert!(trace.contains(input_id));
                }
            }
            other => panic!("should be Proved, but got {other:?}"),
        }
    }

    #[test]
    fn parsed_unsatisfiable_ground_problem_is_proved() {
        let mut symbols = SymbolTable::new();
        let mut sat = Saturation::new();

        let ids = sat
            .add_parsed_tptp_problem("cnf(c1, axiom, p(a)).\ncnf(c2, axiom, ~p(a)).", &mut symbols)
            .unwrap();
        assert_eq!(ids.len(), 2);

        let result = sat.run(1000);
        let SaturationResult::Proved(proved_id) = result else {
            panic!("should be Proved, but got {result:?}");
        };
        let clause = sat.clause_store().get(proved_id);
        assert!(clause.is_empty());
        assert!(matches!(clause.inference.rule, InferenceRule::Resolution { .. }));
    }
}
