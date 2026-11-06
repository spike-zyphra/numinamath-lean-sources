import Mathlib

theorem inequalities_49783 (a b : ℝ) (h : a + b ≥ 1) :
    8 * (a ^ 4 + b ^ 4) ≥ 1 := by 
  have h1 : a ^ 2 + b ^ 2 ≥ 1 / 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
  have h2 : a ^ 4 + b ^ 4 ≥ (a ^ 2 + b ^ 2) ^ 2 / 2 := by 
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have h3 : a ^ 4 + b ^ 4 ≥ 1 / 8 := by 
    nlinarith [h2, h1, sq_nonneg (a ^ 2 - b ^ 2)]
  linarith [h3]