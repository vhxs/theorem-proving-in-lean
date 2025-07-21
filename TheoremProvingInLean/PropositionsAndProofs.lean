-- Chapter 3 exercises
-- (TODO) restructure this into one file per chapter
-- https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#Theorem-Proving-in-Lean-4--Propositions-and-Proofs--Exercises

variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p :=
Iff.intro
  (fun h : p ∧ q => And.intro (And.right h) (And.left h))
  (fun h : q ∧ p => And.intro (And.right h) (And.left h))


example : p ∨ q ↔ q ∨ p :=
Iff.intro
  (fun h : p ∨ q =>
    Or.elim h
      (fun hp : p => Or.intro_right q hp)
      (fun hq : q => Or.intro_left p hq)
  )
  (fun h: q ∨ p =>
    Or.elim h
      (fun hq : q => Or.intro_right p hq)
      (fun hp : p => Or.intro_left q hp)
  )

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
Iff.intro
  (fun h : (p ∧ q) ∧ r =>
    And.intro (And.left (And.left h)) (And.intro (And.right (And.left h)) (And.right h))
  )
  (fun h : p ∧ (q ∧ r) =>
    And.intro (And.intro (And.left h) (And.left (And.right h))) (And.right (And.right h))
  )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
Iff.intro
  (fun h : (p ∨ q) ∨ r =>
    Or.elim h
      (fun hpq : p ∨ q =>
        Or.elim hpq
          (fun hp : p => Or.intro_left (q ∨ r) hp)
          (fun hq : q => Or.intro_right p (Or.intro_left r hq))
      )
      (fun hr : r =>
        Or.intro_right p (Or.intro_right q hr)
      )
  )
  (fun h : p ∨ (q ∨ r) =>
    Or.elim h
      (fun hp : p => Or.intro_left r (Or.intro_left q hp))
      (fun hqr : q ∨ r =>
        Or.elim hqr
          (fun hq : q => Or.intro_left r (Or.intro_right p hq))
          (fun hr : r => Or.intro_right (p ∨ q) hr)
      )
  )

example : p ↔ p := p
