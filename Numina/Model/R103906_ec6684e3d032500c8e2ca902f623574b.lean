import Mathlib

theorem other_205820 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a + b + c + d = 38)
    (h₂ : b + 13 = c)
    (h₃ : c + 16 = d) :
    a + 9 = b := by
  linarith [h₀.1, h₀.2.1, h₀.2.2.1, h₀.2.2.2]