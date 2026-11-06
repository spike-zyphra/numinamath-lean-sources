import Mathlib

theorem inequalities_601168 (a b : ℝ) (h : a^3 + b^3 = 2) : a + b ≤ 2 := by 
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b),
    mul_self_nonneg (a - b)]