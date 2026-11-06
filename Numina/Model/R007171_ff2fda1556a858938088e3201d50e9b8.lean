import Mathlib

theorem algebra_215533 (a b c d m : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < m)
    (h₁ : 2 * (a + b) = m)
    (h₂ : 3 * (b + c) = m)
    (h₃ : 4 * (c + d) = m) :
  12 / 5 * (a + d) = m := by
  linarith