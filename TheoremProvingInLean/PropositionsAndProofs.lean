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

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
Iff.intro
  (fun ⟨hp, hqr⟩ =>
    Or.elim hqr
      (fun hq => Or.intro_left (p ∧ r) ⟨hp, hq⟩)
      (fun hr => Or.intro_right (p ∧ q) ⟨hp, hr⟩))
  (fun h =>
    Or.elim h
      (fun ⟨hp, hq⟩ => ⟨hp, Or.intro_left _ hq⟩)
      (fun ⟨hp, hr⟩ => ⟨hp, Or.intro_right _ hr⟩))

example: p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
Iff.intro
  (fun hpqr =>
    Or.elim hpqr
      (fun hp => And.intro (Or.intro_left q hp) (Or.intro_left r hp))
      (fun hqr => And.intro (Or.intro_right p (And.left hqr)) (Or.intro_right p (And.right hqr)))
  )
  (fun ⟨hpq, hpr⟩ =>
    Or.elim hpq
      (fun hp => Or.intro_left (q ∧ r) hp)
      (fun hq =>
        Or.elim hpr
          (fun hp => Or.inl hp)
          (fun hr => Or.inr (And.intro hq hr))
      )
  )
