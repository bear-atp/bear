;; Barbara syllogism, chained twice — pure FOL, no function symbols.
;; Axioms:
;;   All men are mortal:      man(X) -> mortal(X)
;;   All mortals are animals: mortal(X) -> animal(X)
;;   Socrates is a man:       man(socrates)
;; Goal: Socrates is an animal. Negated goal: not(animal(socrates))
(clause (not (man X)) (mortal X))
(clause (not (mortal X)) (animal X))
(clause (man socrates))
(clause (not (animal socrates)))