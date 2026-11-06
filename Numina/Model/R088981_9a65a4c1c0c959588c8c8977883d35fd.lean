import Mathlib

theorem algebra_262108 : ∃ f : ℝ → ℝ, Function.Surjective f ∧ ∀ x y, f (x + y) - f x - f y = 0 ∨ f (x + y) - f x - f y = 1 := by
  use (fun x => x)
  constructor
  · -- Show f is surjective
    apply Function.surjective_id
  · -- Show functional equation condition
    intro x y
    left
    simp