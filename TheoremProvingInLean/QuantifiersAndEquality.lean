-- Chapter 4 exercises
-- https://leanprover.github.io/theorem_proving_in_lean4/Quantifiers-and-Equality/#Theorem-Proving-in-Lean-4--Quantifiers-and-Equality--Exercises

variable {α : Type} (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
Iff.intro
  (fun haxpxqx =>
    And.intro
      (fun x => And.left (haxpxqx x))
      (fun x => And.right (haxpxqx x))
  )
  (fun ⟨ haxpx, haxqx ⟩ =>
    (fun x => And.intro (haxpx x) (haxqx x))
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (fun hapxqx =>
    (fun haxpx =>
      (fun hx =>
        (hapxqx hx) (haxpx hx)
      )
    )
  )

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun h =>
    (fun x =>
      Or.elim h
        (fun haxpx => Or.inl (haxpx x))
        (fun haxqx => Or.inr (haxqx x))
    )
  )

example : α → ((∀ _ : α, r) ↔ r) :=
  (fun h =>
    Iff.intro
      (fun haxar => (haxar h))
      (fun hr => (fun _ => hr))
  )
