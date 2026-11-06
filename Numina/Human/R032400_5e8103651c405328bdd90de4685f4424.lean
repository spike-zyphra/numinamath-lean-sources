import Mathlib

theorem algebra_181496 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : 6 * (a + b - d) = 1)
    (h₂ : 5 * (a + c - d) = 1)
    (h₃ : 4 * (b + c - d) = 1)
    (h₄ : 3 * (a + b + c - d) = 1) :
    1 / (a + b + c) = 2 + 14/23 := by
  have : a + b + c > 0 := by linarith
  field_simp
  linarith
