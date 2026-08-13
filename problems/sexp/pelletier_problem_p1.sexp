;; Propositional hypothetical syllogism (in the spirit of Pelletier P1):
;;   (p -> q) & (q -> r) -> (p -> r)
;; Negated goal: p is true, r is false.
;; All atoms are 0-arity predicates (propositions), so there's no
;; unification/Skolem-function blowup at all — pure ground resolution.
(clause (not p) (q))     ; p -> q
(clause (not q) (r))     ; q -> r
(clause p)                ; negated goal, part 1: p
(clause (not r))          ; negated goal, part 2: not r