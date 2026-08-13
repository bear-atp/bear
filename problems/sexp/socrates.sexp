; Classic syllogism: All men are mortal. Socrates is a man. Therefore Socrates is mortal.
; Proven via refutation: negate the goal, find a contradiction (empty clause).

(clause (not (man X)) (mortal X))   ; axiom: man(x) -> mortal(x)
(clause (man socrates))             ; axiom: socrates is a man
(clause (not (mortal socrates)))    ; negated goal: socrates is NOT mortal