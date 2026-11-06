import Mathlib

theorem algebra_598997 (a b c : ℝ) (h₀ : b + c ≠ 0) (h₁ : c + a ≠ 0) (h₂ : a + b ≠ 0) :
    a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) - (a + b + c) / 2 =
    ((2 * a - b - c)^2 / (b + c) + (2 * b - c - a)^2 / (c + a) +
     (2 * c - a - b)^2 / (a + b)) / 4 := by
  field_simp
  ring