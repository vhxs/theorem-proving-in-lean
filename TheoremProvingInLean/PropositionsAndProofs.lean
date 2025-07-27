-- Chapter 3 exercises
-- https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#Theorem-Proving-in-Lean-4--Propositions-and-Proofs--Exercises

open Classical

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

example: (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro
  (fun hpqr: (p → (q → r)) =>
    (fun hpq: p ∧ q => hpqr (And.left hpq) (And.right hpq))
  )
  (fun h: p ∧ q → r =>
    (fun p =>
      (fun q =>
        (h (And.intro p q))
      )
    )
  )


example: ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
Iff.intro
  (fun hpqr: (p ∨ q) → r =>
    And.intro
      (fun hp: p => hpqr (Or.intro_left q hp))
      (fun hq: q => hpqr (Or.intro_right p hq))
  )
  (fun h: (p → r) ∧ (q → r) =>
    (fun hpq: p ∨ q =>
      Or.elim hpq
        (fun hp: p => (And.left h) hp)
        (fun hq: q => (And.right h) hq)
    )
  )

example: ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
Iff.intro
  (fun hnpq: ¬(p ∨ q) =>
    And.intro (fun hp: p => hnpq (Or.inl hp)) (fun hq: q => hnpq (Or.inr hq))
  )
  (fun ⟨ hnp, hnq ⟩ =>
    (fun hpq: p ∨ q =>
      Or.elim hpq
        (fun hp: p => hnp hp)
        (fun hq: q => hnq hq)
    )
  )

example: ¬p ∨ ¬q → ¬(p ∧ q) :=
(fun hnpnq: ¬p ∨ ¬q =>
  fun hpq: p ∧ q =>
    Or.elim hnpnq
      (fun hnp: ¬p => hnp (And.left hpq))
      (fun hnq: ¬q => hnq (And.right hpq))
)

example: ¬(p ∧ ¬p) :=
(fun hpnp: p ∧ ¬p =>
  let hp := And.left hpnp
  let hnp := And.right hpnp
  hnp hp
)

example : p ∧ ¬q → ¬(p → q) :=
(fun hpnq: p ∧ ¬q =>
  fun hpiq: p → q =>
    (And.right hpnq) (hpiq (And.left hpnq))
)

example : ¬p → (p → q) :=
(fun hnp: ¬p =>
  (fun hp: p =>
    False.elim (hnp hp)
  )
)

example : (¬p ∨ q) → (p → q) :=
(fun hnpq : ¬p ∨ q =>
  (fun hp: p =>
    Or.elim hnpq
      (fun hnp: ¬p => False.elim (hnp hp))
      (fun hq: q => hq)
  )
)

example : p ∨ False ↔ p :=
Iff.intro
  (fun hpf: p ∨ False =>
    Or.elim hpf
      (fun hp: p => hp)
      (fun hf: False => False.elim hf)
  )
  (fun hp: p => Or.inl hp)

example : p ∧ False ↔ False :=
Iff.intro
  (fun hpf: p ∧ False => And.right hpf)
  (fun hf: False => False.elim hf)

example : (p → q) → (¬q → ¬p) :=
(fun hpiq: p → q =>
  (fun hnq: ¬q =>
    (fun hp: p =>
      hnq (hpiq hp)
    )
  )
)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r =>
    Or.elim (em p)
      (fun hp : p =>
        Or.elim (h hp)
          (fun hq : q => Or.inl (fun _ => hq))
          (fun hr : r => Or.inr (fun _ => hr)))
      (fun hnp : ¬p =>
        Or.inl (fun hp => False.elim (hnp hp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun hnpq : ¬(p ∧ q) =>
    Or.elim (em p)
      (fun hp: p => Or.intro_right (¬p) (fun hq: q => hnpq (And.intro hp hq)))
      (fun hnp: ¬p => Or.intro_left (¬q) hnp)
  )

example : ¬(p → q) → p ∧ ¬q :=
  (fun hnpiq: ¬(p → q) =>
    Or.elim (em p)
      (fun hp: p =>
        Or.elim (em q)
          (fun hq: q => False.elim (hnpiq (fun _ => hq)))
          (fun hnq: ¬q => And.intro hp hnq)
      )
      (fun hnp: ¬p =>
        False.elim (hnpiq (fun hp => False.elim (hnp hp)))
      )
  )

example : (p → q) → (¬p ∨ q) :=
 (fun hpq: p → q =>
  Or.elim (em p)
    (fun hp: p => Or.intro_right (¬p) (hpq hp))
    (fun hnp: ¬p => Or.intro_left q hnp)
 )

example : (¬q → ¬p) → (p → q) :=
  (fun hnqnp: ¬q → ¬p =>
    (fun hp: p =>
      Or.elim (em q)
        (fun hq: q => hq)
        (fun hnq: ¬q => False.elim (hnqnp hnq hp))
    )
  )

example : p ∨ ¬p :=
  Or.elim (em p)
    (fun hp: p => Or.inl hp)
    (fun hnp: ¬p => Or.inr hnp)

example : ((p → q) → p) → p :=
  (fun hpqp : (p → q) → p =>
    Or.elim (em p)
      (fun hp: p => hp)
      (fun hnp: ¬p => hpqp (fun hp => False.elim (hnp hp)))
  )
