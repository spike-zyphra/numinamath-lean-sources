import Mathlib

theorem algebra_221383 (a b : ℤ) (ha : a ≠ 0) (h : ∀ x : ℤ, (a * x ^ 2 + b * x + 14) ^ 2 + (b * x ^ 2 + a * x + 8) ^ 2 = 0) :
    a = -2 ∧ b = -6 ∧ b = -5 := by
  have h1 := h 0
  norm_num at h1 
  all_goals omega