import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_145523 (f : ℝ → ℝ → ℝ)
  (h₀ : f = λ x y => y^2 - x^2) :
  ∃ x y, x - 2 * y + 3 = 0 ∧ f x y = 3 ∧
  (∀ x y, x - 2 * y + 3 = 0 → f x y ≤ 3) := by
    use 1, 2
    constructor
    · -- Check the constraint.
      norm_num
    constructor
    · -- Check f(1, 2) = 3.
      rw [h₀]
      norm_num
    · -- Show that for all x, y satisfying the constraint, f(x, y) ≤ 3.
      intro x y h
      rw [h₀]
      have h1 : x - 2 * y + 3 = 0 := h
      have hx : x = 2 * y - 3 := by
        linarith
      simp [hx]
      nlinarith [sq_nonneg (y - 2)]