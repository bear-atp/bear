//! S-expression-based input format parser — a temporary stand-in before a
//! //! real TPTP parser lands in v0.2 (README §2). Deliberately built to follow
//! TPTP's own conventions from day one (uppercase = variable,
//! lowercase = constant/function/predicate) so switching to TPTP later is a
//! grammar change, not a mental-model change.
//!
//! # Syntax
//!
//! One problem = a sequence of top-level forms, each shaped like
//! `(clause <literal>...)`. Example:
//!
//! ```text
//! ; comments start with a semicolon and run to end of line
//! (clause (not (man X)) (mortal X))   ; man(x) -> mortal(x)
//! (clause (man socrates))
//! (clause (not (mortal socrates)))    ; negated goal
//! ```
//!
//! - **Literal**: `(pred arg...)` for positive, `(not (pred arg...))` for
//!   negative. A propositional predicate (arity 0) may be written without
//!   parens, e.g. `p` or `(not p)`.
//! - **Term**: `name` (a variable if it starts with an uppercase letter or
//!   `_`, a constant otherwise) or `(f arg...)` for function application.
//! - **Variables are scoped per-clause**: `X` in the first clause is
//!   UNRELATED to `X` in the second clause (this matches `VarId` being
//!   scoped per-clause everywhere else — see `term::VarId`). Cross-clause
//!   safety (rename-apart) remains `inference`'s job, not this parser's.
//! - `(clause)` (no literals at all) is valid and represents the empty
//!   clause `⊥` directly as input — a rarely-used edge case, mainly useful
//!   for tests.

use std::collections::HashMap;

use crate::clause::Literal;
use crate::term::{ SymbolTable, TermArena, TermId, VarId };

/// A parse error, carrying a 1-indexed line number for easy debugging.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl ParseError {
    fn new(line: usize, message: impl Into<String>) -> Self {
        Self { line, message: message.into() }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "baris {}: {}", self.line, self.message)
    }
}

impl std::error::Error for ParseError {}

// ---------------------------------------------------------------------
// Tokenizer
// ---------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum Token {
    LParen,
    RParen,
    Symbol(String),
}

/// Turn raw source text into a flat token stream, each tagged with the
/// (1-indexed) line it started on.
///
/// **Algorithm:** single left-to-right scan over `chars()` with a `peekable`
/// iterator, branching on the current character:
/// - whitespace (space/tab/CR) -> consumed, no token emitted
/// - `\n` -> consumed, `line` counter incremented, no token emitted
/// - `;` -> consume everything up to (but not including) the next `\n`
///   (comment, no token emitted)
/// - `(` / `)` -> emit `LParen`/`RParen` directly
/// - anything else -> greedily consume characters into a `Symbol` token
///   until hitting whitespace, `(`, `)`, or `;` (this is what makes `(man
///   socrates)` tokenize into three separate tokens even with no space
///   before/after the parens: `(` immediately terminates the preceding
///   symbol-scan, so `clause(foo` would ALSO correctly split into `clause`
///   + `(` + `foo` even without a space — parens are always their own
///   token, never absorbed into a symbol).
///
/// **Complexity:** O(n) in input length — every character is visited
/// exactly once (via `peek`/`next`, no backtracking).
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
            ';' => {
                // Comment to end of line — consumed, no token produced.
                while let Some(&c2) = chars.peek() {
                    if c2 == '\n' {
                        break;
                    }
                    chars.next();
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
            _ => {
                let start_line = line;
                let mut sym = String::new();
                while let Some(&c2) = chars.peek() {
                    if c2.is_whitespace() || c2 == '(' || c2 == ')' || c2 == ';' {
                        break;
                    }
                    sym.push(c2);
                    chars.next();
                }
                tokens.push((Token::Symbol(sym), start_line));
            }
        }
    }

    Ok(tokens)
}

// ---------------------------------------------------------------------
// S-expression AST
// ---------------------------------------------------------------------

/// One node of the raw S-expression tree, before any semantic
/// interpretation (before we know whether an atom is a variable, constant,
/// predicate name, or the literal `not`/`clause` keyword — that
/// disambiguation happens entirely in the semantic pass below).
#[derive(Debug, Clone)]
struct Sexpr {
    line: usize,
    kind: SexprKind,
}

#[derive(Debug, Clone)]
enum SexprKind {
    Atom(String),
    List(Vec<Sexpr>),
}

struct SexprParser<'a> {
    tokens: &'a [(Token, usize)],
    pos: usize,
}

impl<'a> SexprParser<'a> {
    /// Parse the ENTIRE token stream into a sequence of top-level `Sexpr`
    /// forms (normally one `Sexpr::List` per `(clause ...)` form).
    ///
    /// **Complexity:** O(n) in token count — each token is consumed exactly
    /// once across all the recursive `parse_expr` calls this makes.
    fn parse_all(&mut self) -> Result<Vec<Sexpr>, ParseError> {
        let mut exprs = Vec::new();
        while self.pos < self.tokens.len() {
            exprs.push(self.parse_expr()?);
        }
        Ok(exprs)
    }

    /// Parse ONE S-expression starting at `self.pos`, advancing `self.pos`
    /// past it.
    ///
    /// **Algorithm:** classic recursive-descent parser for a trivial
    /// grammar (`expr := atom | '(' expr* ')'`):
    /// - `LParen` -> recursively parse zero or more sub-expressions until
    ///   hitting the matching `RParen` (missing `RParen` before running out
    ///   of tokens -> error, reported at the position of the OPENING paren
    ///   so the error message points at "which `(` never got closed").
    /// - Bare `RParen` (with no preceding unmatched `LParen`) -> error.
    /// - `Symbol` -> wrap directly into `Sexpr::Atom`.
    /// - End of token stream where an expression was expected -> error.
    ///
    /// **Complexity:** O(size of the subtree parsed) — each nested list
    /// recurses once per child.
    fn parse_expr(&mut self) -> Result<Sexpr, ParseError> {
        match self.tokens.get(self.pos) {
            Some((Token::LParen, line)) => {
                let line = *line;
                self.pos += 1;
                let mut items = Vec::new();
                loop {
                    match self.tokens.get(self.pos) {
                        Some((Token::RParen, _)) => {
                            self.pos += 1;
                            break;
                        }
                        Some(_) => items.push(self.parse_expr()?),
                        None => {
                            return Err(
                                ParseError::new(
                                    line,
                                    "tanda kurung tidak lengkap: EOF sebelum ')' penutup"
                                )
                            );
                        }
                    }
                }
                Ok(Sexpr { line, kind: SexprKind::List(items) })
            }
            Some((Token::RParen, line)) => {
                Err(ParseError::new(*line, "')' tak terduga tanpa '(' pembuka"))
            }
            Some((Token::Symbol(s), line)) => {
                let expr = Sexpr { line: *line, kind: SexprKind::Atom(s.clone()) };
                self.pos += 1;
                Ok(expr)
            }
            None => Err(ParseError::new(0, "input kosong atau EOF tak terduga")),
        }
    }
}

// ---------------------------------------------------------------------
// Semantic pass: Sexpr -> Literal/Clause
// ---------------------------------------------------------------------

/// The ENTIRE variable-vs-constant disambiguation rule for this whole
/// parser lives in this one function: an identifier is a variable if its
/// first character is uppercase or `_`, otherwise it's a
/// constant/function/predicate name. (TPTP/Prolog convention — see module
/// doc comment.)
fn is_variable_name(s: &str) -> bool {
    s.chars()
        .next()
        .map(|c| c.is_uppercase() || c == '_')
        .unwrap_or(false)
}

/// Per-clause parsing context: owns the mutable arena/symbol-table borrows
/// needed to actually BUILD terms, plus the variable-name -> `VarId` mapping
/// that's local to ONE clause (a fresh `ClauseCtx` is created per clause in
/// `parse_clause` below, specifically so this map resets and variable
/// numbering restarts at 0 for every new clause — matching `VarId`'s
/// per-clause scoping everywhere else in the codebase).
struct ClauseCtx<'a> {
    arena: &'a mut TermArena,
    symbols: &'a mut SymbolTable,
    var_map: HashMap<String, VarId>,
    next_var: VarId,
}

impl<'a> ClauseCtx<'a> {
    /// Get-or-assign a `VarId` for a variable NAME within this clause.
    ///
    /// **Algorithm:** same get-or-create pattern as `SymbolTable::intern` /
    /// `TermArena::mk_var` — check `var_map` first, assign the next
    /// sequential id on a miss.
    ///
    /// **Complexity:** O(1) average.
    fn var_id(&mut self, name: &str) -> VarId {
        if let Some(&id) = self.var_map.get(name) {
            return id;
        }
        let id = self.next_var;
        self.next_var += 1;
        self.var_map.insert(name.to_string(), id);
        id
    }

    /// Parse one S-expression as a TERM (used for literal arguments, and
    /// recursively for nested function-application arguments).
    ///
    /// **Algorithm:**
    /// - `Atom(name)`: `is_variable_name(name)` decides everything —
    ///   variable -> resolve/assign a `VarId` via `var_id`, then
    ///   `arena.mk_var`; otherwise -> intern `name` as a `SymbolId` and
    ///   build a zero-arg `App` (i.e. a constant) via `arena.mk_app`.
    /// - `List(items)`: the first item MUST be an atom naming the function
    ///   symbol (a list-headed application like `((f x) y)` is rejected —
    ///   there's no higher-order application in this format). That head
    ///   must NOT look like a variable name (`(X a)` is a parse error, not
    ///   "call the function bound to X" — this format has no such concept).
    ///   Every remaining item is recursively parsed as a term (arguments),
    ///   then the whole thing becomes one `arena.mk_app` call.
    ///
    /// **Complexity:** O(size of the term being parsed).
    fn parse_term(&mut self, expr: &Sexpr) -> Result<TermId, ParseError> {
        match &expr.kind {
            SexprKind::Atom(name) => {
                if is_variable_name(name) {
                    let id = self.var_id(name);
                    Ok(self.arena.mk_var(id))
                } else {
                    let sym = self.symbols.intern(name);
                    Ok(self.arena.mk_app(sym, &[]))
                }
            }
            SexprKind::List(items) => {
                let Some(head) = items.first() else {
                    return Err(ParseError::new(expr.line, "'()' bukan term yang valid"));
                };
                let SexprKind::Atom(head_name) = &head.kind else {
                    return Err(
                        ParseError::new(
                            head.line,
                            "kepala function application harus simbol, bukan list"
                        )
                    );
                };
                if is_variable_name(head_name) {
                    return Err(
                        ParseError::new(
                            head.line,
                            format!(
                                "'{head_name}' diawali huruf besar (dianggap variable), tidak bisa dipakai sebagai nama function"
                            )
                        )
                    );
                }
                let sym = self.symbols.intern(head_name);
                let mut args = Vec::with_capacity(items.len() - 1);
                for a in &items[1..] {
                    args.push(self.parse_term(a)?);
                }
                Ok(self.arena.mk_app(sym, &args))
            }
        }
    }

    /// Parse `(pred arg...)` or bare `pred` (arity 0) into a raw
    /// `(SymbolId, Vec<TermId>)` pair — the shared building block used by
    /// both plain positive literals AND the inner form of `(not ...)`
    /// (see `parse_literal` below).
    ///
    /// **Algorithm:** structurally almost identical to `parse_term`'s
    /// `List` branch, except this one ALSO accepts a bare `Atom` directly
    /// (representing a zero-arity predicate written without parens, e.g.
    /// `p` instead of `(p)`) — `parse_term` never allows a bare atom to
    /// mean "zero-arg application", only literals get that shorthand.
    ///
    /// **Complexity:** O(size of the literal's arguments).
    fn parse_predicate_app(&mut self, expr: &Sexpr) -> Result<(u32, Vec<TermId>), ParseError> {
        match &expr.kind {
            SexprKind::Atom(name) => {
                if is_variable_name(name) {
                    return Err(
                        ParseError::new(
                            expr.line,
                            format!(
                                "'{name}' diawali huruf besar (dianggap variable), tidak bisa dipakai sebagai nama predicate"
                            )
                        )
                    );
                }
                Ok((self.symbols.intern(name), Vec::new()))
            }
            SexprKind::List(items) => {
                let Some(head) = items.first() else {
                    return Err(ParseError::new(expr.line, "'()' bukan literal yang valid"));
                };
                let SexprKind::Atom(head_name) = &head.kind else {
                    return Err(
                        ParseError::new(head.line, "kepala predicate harus simbol, bukan list")
                    );
                };
                if is_variable_name(head_name) {
                    return Err(
                        ParseError::new(
                            head.line,
                            format!(
                                "'{head_name}' diawali huruf besar (dianggap variable), tidak bisa dipakai sebagai nama predicate"
                            )
                        )
                    );
                }
                let pred = self.symbols.intern(head_name);
                let mut args = Vec::with_capacity(items.len() - 1);
                for a in &items[1..] {
                    args.push(self.parse_term(a)?);
                }
                Ok((pred, args))
            }
        }
    }

    /// Parse one S-expression as a LITERAL (positive or negative).
    ///
    /// **Algorithm:** peek at whether this is a `(not ...)` form (a list
    /// whose head atom is literally the string `"not"`) — if so, require
    /// EXACTLY one inner argument, parse THAT as a predicate application,
    /// and wrap it negative. Anything else (including a bare atom, or a
    /// list whose head is some other predicate name) is parsed as a
    /// predicate application directly and wrapped positive.
    ///
    /// Note `"not"` is not a reserved word anywhere except this exact
    /// position (as the head of the OUTERMOST form being parsed as a
    /// literal) — a predicate genuinely named `not` used elsewhere (e.g. as
    /// a function argument) would parse as an ordinary symbol, since
    /// `parse_term`/`parse_predicate_app` never special-case it.
    ///
    /// **Complexity:** O(size of the literal).
    fn parse_literal(&mut self, expr: &Sexpr) -> Result<Literal, ParseError> {
        if let SexprKind::List(items) = &expr.kind {
            if let Some(Sexpr { kind: SexprKind::Atom(head_name), .. }) = items.first() {
                if head_name == "not" {
                    if items.len() != 2 {
                        return Err(
                            ParseError::new(
                                expr.line,
                                "'not' butuh tepat 1 argumen: (not (pred arg...))"
                            )
                        );
                    }
                    let (pred, args) = self.parse_predicate_app(&items[1])?;
                    return Ok(Literal::negative(pred, args));
                }
            }
        }
        let (pred, args) = self.parse_predicate_app(expr)?;
        Ok(Literal::positive(pred, args))
    }
}

/// Parse ONE top-level `(clause <literal>...)` form into `Vec<Literal>`.
///
/// **Algorithm:**
/// 1. Confirm `form` is a non-atom list whose FIRST element is literally the
///    atom `"clause"` (anything else -> a descriptive error pointing at the
///    offending form/line).
/// 2. Build a FRESH `ClauseCtx` (fresh `var_map`, `next_var` reset to 0) —
///    this is the exact mechanism that makes variable scope reset per
///    clause, matching `VarId`'s documented semantics.
/// 3. Parse every remaining item as a literal via `ClauseCtx::parse_literal`,
///    collecting them in order.
///
/// **Complexity:** O(size of the clause).
fn parse_clause(
    form: &Sexpr,
    arena: &mut TermArena,
    symbols: &mut SymbolTable
) -> Result<Vec<Literal>, ParseError> {
    let items = match &form.kind {
        SexprKind::List(items) => items,
        SexprKind::Atom(_) => {
            return Err(
                ParseError::new(
                    form.line,
                    "form top-level harus berbentuk (clause <literal>...), bukan atom lepas"
                )
            );
        }
    };

    match items.first() {
        Some(Sexpr { kind: SexprKind::Atom(s), .. }) if s == "clause" => {}
        Some(other) => {
            return Err(ParseError::new(other.line, "form top-level harus diawali simbol 'clause'"));
        }
        None => {
            return Err(
                ParseError::new(form.line, "form top-level kosong, harus (clause <literal>...)")
            );
        }
    }

    let mut ctx = ClauseCtx { arena, symbols, var_map: HashMap::new(), next_var: 0 };
    let mut literals = Vec::with_capacity(items.len().saturating_sub(1));
    for lit_expr in &items[1..] {
        literals.push(ctx.parse_literal(lit_expr)?);
    }
    Ok(literals)
}

/// Parse an entire problem (many `(clause ...)` forms) into a list of
/// clauses, each as `Vec<Literal>`. Terms are built directly into `arena`,
/// predicate/function/constant names are interned into `symbols` — both
/// owned by the caller (typically the arena/symbol-table of a `Saturation`
/// session, see `Saturation::add_parsed_problem`).
///
/// **Algorithm:** three-stage pipeline, each stage fully consuming the
/// previous stage's output before the next begins (not interleaved/
/// streaming — fine at this problem size, would need rethinking for huge
/// files):
/// 1. `tokenize` — text -> flat token stream.
/// 2. `SexprParser::parse_all` — tokens -> raw `Sexpr` forest (one tree per
///    top-level form).
/// 3. `parse_clause` per top-level form — `Sexpr` -> `Vec<Literal>`,
///    actually populating `arena`/`symbols` as a side effect.
///
/// **Complexity:** O(n) in input length for tokenizing + S-expression
/// parsing, plus O(total term size across the whole problem) for the
/// semantic pass — overall linear in input size.
pub fn parse_problem(
    input: &str,
    arena: &mut TermArena,
    symbols: &mut SymbolTable
) -> Result<Vec<Vec<Literal>>, ParseError> {
    let tokens = tokenize(input)?;
    let mut parser = SexprParser { tokens: &tokens, pos: 0 };
    let forms = parser.parse_all()?;

    let mut clauses = Vec::with_capacity(forms.len());
    for form in &forms {
        clauses.push(parse_clause(form, arena, symbols)?);
    }
    Ok(clauses)
}

// TODO(v0.2 — real TPTP support): this whole file is a stopgap. A real TPTP
// parser needs to additionally handle: FOF (full first-order, with explicit
// quantifiers `!`/`?` and connectives `&`/`|`/`=>`/`<=>`, not pre-flattened
// CNF like this format assumes), `include()` directives pulling in other
// files, role annotations (`axiom`/`conjecture`/`negated_conjecture`/etc —
// currently this format has no concept of "this clause is the goal", which
// also blocks the ML roadmap's "goal similarity" feature, see the TODO in
// clause.rs), and proper handling of TPTP's `$`-prefixed reserved terms
// (`$true`, `$false`, arithmetic). Don't try to evolve THIS file into that
// incrementally — it'll likely be a genuinely separate module (`tptp.rs`)
// sitting alongside this one, since the grammar is meaningfully bigger, not
// just "this format plus a few more cases".

// TODO(v0.2 — error messages): `ParseError` only carries a line number, not
// a column/byte-offset. For single-line clauses (the common case) this is
// usually enough to find the problem, but for anything spanning many tokens
// on one line, "line 4: 'X' cannot be used as..." still requires some
// hunting. Worth adding a column/token-span if this becomes annoying in
// practice — not urgent, tests currently only assert on `.line`, not on
// exact column positions.

#[cfg(test)]
mod tests {
    use crate::clause::InferenceRule;
    use crate::saturation::{ Saturation, SaturationResult };
    use crate::term::{ SymbolTable, TermArena, TermData };

    #[test]
    fn parses_single_ground_positive_literal() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::parser
            ::parse_problem("(clause (man socrates))", &mut arena, &mut symbols)
            .unwrap();

        assert_eq!(clauses.len(), 1);
        let clause = &clauses[0];
        assert_eq!(clause.len(), 1);
        assert!(clause[0].is_positive());
        assert_eq!(clause[0].display(&arena, &symbols), "man(socrates)");
    }

    #[test]
    fn parses_negative_literal_via_not() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::parser
            ::parse_problem("(clause (not (mortal socrates)))", &mut arena, &mut symbols)
            .unwrap();

        let clause = &clauses[0];
        assert!(clause[0].is_negative());
        assert_eq!(clause[0].display(&arena, &symbols), "~mortal(socrates)");
    }

    #[test]
    fn parses_propositional_literal_without_parens() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::parser
            ::parse_problem("(clause p (not q))", &mut arena, &mut symbols)
            .unwrap();

        let clause = &clauses[0];
        assert_eq!(clause.len(), 2);
        assert_eq!(clause[0].display(&arena, &symbols), "p");
        assert_eq!(clause[1].display(&arena, &symbols), "~q");
    }

    #[test]
    fn empty_clause_form_parses_to_bottom() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::parser::parse_problem("(clause)", &mut arena, &mut symbols).unwrap();

        assert_eq!(clauses.len(), 1);
        assert!(clauses[0].is_empty());
    }

    #[test]
    fn variable_is_consistent_within_one_clause() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::parser
            ::parse_problem("(clause (not (man X)) (mortal X))", &mut arena, &mut symbols)
            .unwrap();

        let clause = &clauses[0];
        assert_eq!(clause.len(), 2);
        // Both literals use the same variable X -> argument TermIds must be identical.
        assert_eq!(clause[0].args[0], clause[1].args[0]);
        assert!(matches!(arena.get(clause[0].args[0]), TermData::Var(_)));
    }

    #[test]
    fn variable_scope_is_independent_across_clauses() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::parser
            ::parse_problem("(clause (p X))\n(clause (q X))", &mut arena, &mut symbols)
            .unwrap();

        // X in the first clause and X in the second clause do NOT have to be the same TermId
        // (variable scope is per-clause, each starting numbering from 0 again).
        // What matters: each remains a valid variable.
        assert!(matches!(arena.get(clauses[0][0].args[0]), TermData::Var(_)));
        assert!(matches!(arena.get(clauses[1][0].args[0]), TermData::Var(_)));
    }

    #[test]
    fn parses_nested_function_application() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let clauses = crate::parser
            ::parse_problem("(clause (p (f X a)))", &mut arena, &mut symbols)
            .unwrap();

        let clause = &clauses[0];
        assert_eq!(clause[0].display(&arena, &symbols), "p(f(X0, a))");
    }

    #[test]
    fn comments_and_extra_whitespace_are_ignored() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let input =
            "
        ; this is a full-line comment
        (clause   (man socrates))   ; end-of-line comment as well
        ;(clause (not (man socrates))) -- this line is commented out, not parsed
    ";
        let clauses = crate::parser::parse_problem(input, &mut arena, &mut symbols).unwrap();
        assert_eq!(clauses.len(), 1);
    }

    #[test]
    fn multiple_clauses_are_all_parsed_in_order() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let input = "(clause (p a))\n(clause (q b))\n(clause (r c))";
        let clauses = crate::parser::parse_problem(input, &mut arena, &mut symbols).unwrap();
        assert_eq!(clauses.len(), 3);
    }

    // ---------- error cases ----------

    #[test]
    fn error_on_unbalanced_parens_missing_close() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let err = crate::parser
            ::parse_problem("(clause (man socrates)", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("kurung") || err.message.contains("EOF"));
    }

    #[test]
    fn error_on_unexpected_closing_paren() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let err = crate::parser
            ::parse_problem("(clause (man socrates)))", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("')'"));
    }

    #[test]
    fn error_when_top_level_form_missing_clause_keyword() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let err = crate::parser
            ::parse_problem("(man socrates)", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("clause"));
    }

    #[test]
    fn error_when_variable_used_as_predicate_name() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        // X starts with an uppercase letter -> treated as a variable, invalid as a predicate name.
        let err = crate::parser
            ::parse_problem("(clause (X a))", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("variable"));
    }

    #[test]
    fn error_when_variable_used_as_function_name() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let err = crate::parser
            ::parse_problem("(clause (p (X a)))", &mut arena, &mut symbols)
            .unwrap_err();
        assert!(err.message.contains("variable"));
    }

    #[test]
    fn error_message_includes_line_number() {
        let mut arena = TermArena::new();
        let mut symbols = SymbolTable::new();
        let input = "(clause (man socrates))\n(clause (X a))"; // error on line 2
        let err = crate::parser::parse_problem(input, &mut arena, &mut symbols).unwrap_err();
        assert_eq!(err.line, 2);
    }

    // ---------- full integration: parse -> Saturation ----------

    #[test]
    fn parsed_problem_can_be_proved_end_to_end() {
        let mut symbols = SymbolTable::new();
        let mut sat = Saturation::new();

        let input =
            "
        (clause (not (man X)) (mortal X))
        (clause (man socrates))
        (clause (not (mortal socrates)))
    ";
        let ids = sat.add_parsed_problem(input, &mut symbols).unwrap();
        assert_eq!(ids.len(), 3);

        let result = sat.run(1000);
        match result {
            SaturationResult::Proved(id) => {
                let trace = sat.proof_trace(id);
                assert!(trace.len() >= 4);
                // All 3 input clauses must be used in the proof.
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
            .add_parsed_problem("(clause (p a))\n(clause (not (p a)))", &mut symbols)
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
