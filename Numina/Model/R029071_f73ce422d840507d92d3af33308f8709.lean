import Mathlib

theorem algebra_297312 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a * b * c = 1) :
    ∃ n, n > 3 / 2 ∧ a = n ∨ b = n ∨ c = n := by
  use b
  right
  left
  rfl