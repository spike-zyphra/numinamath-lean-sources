import Mathlib

theorem inequalities_291481 (a b : ℝ) (h : a * b ≥ a ^ 3 + b ^ 3) : a + b ≤ 1 := by 
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a - b), sq_nonneg (a + b),
    mul_self_nonneg (a + 1), mul_self_nonneg (b + 1)]