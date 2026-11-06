import Mathlib

theorem algebra_9374 (x y z : ℝ) (h : x + 3 * y + 2 * z = 6) :
    x ^ 2 + 9 * y ^ 2 - 2 * x - 6 * y + 4 * z ≤ 8 ↔ (x - 2) ^ 2 + (3 * y - 2) ^ 2 ≤ 4 := by 
  have h1 : 4 * z = 12 - 2 * x - 6 * y := by 
    linarith
  constructor
  · -- Assume the inequality holds, prove the transformed version
    intro h_ineq
    nlinarith [sq_nonneg (x - 2), sq_nonneg (3 * y - 2), h_ineq, h1]
  · -- Assume the transformed inequality, prove the original
    intro h_ineq
    nlinarith [sq_nonneg (x - 2), sq_nonneg (3 * y - 2), h_ineq, h1]