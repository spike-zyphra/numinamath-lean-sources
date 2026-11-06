import Mathlib

theorem number_theory_271238 (a b c d : ℤ) (h : a * d - b * c = 1) (h₁ : a * c + b * d ≠ 0) : IsCoprime (a ^ 2 + b ^ 2) (a * c + b * d) := by
  use c ^ 2 + d ^ 2
  use -(a * c + b * d)
  have h2 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by
    nlinarith
  have h3 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = 1 := by
    rw [h2]
    rw [h]
    all_goals norm_num
  linarith