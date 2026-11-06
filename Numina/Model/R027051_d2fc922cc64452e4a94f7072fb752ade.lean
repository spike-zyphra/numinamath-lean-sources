import Mathlib

theorem inequalities_54609 (a b c : ℝ) (h₀ : ¬(a = b ∧ b = c)) (h₁ : a + b + c = 3) (h₂ : 1 / a + 1 / b + 1 / c = 3) :
    ∃ x, x < 0 ∧ x = a ∨ x = b ∨ x = c := by
  use b
  right
  left
  rfl