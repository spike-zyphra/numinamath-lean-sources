import Mathlib

theorem algebra_190652 (a b : ℝ) (h : a^2 ≥ 8 * b) :
    (1 - a)^2 + (1 - 2 * b)^2 + (a - 2 * b)^2 ≥ 9 / 8 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1/8), sq_nonneg (a - 2 * b), 
          mul_nonneg (show 0 ≤ (a - 1) ^ 2 by apply sq_nonneg) (show 0 ≤ (a - 2 * b) ^ 2 by apply sq_nonneg), 
          mul_nonneg (show 0 ≤ (a - 1) ^ 2 by apply sq_nonneg) (show 0 ≤ (1 - 2 * b) ^ 2 by apply sq_nonneg),
          sq_nonneg (a - 2 * b - (1 - 2 * b)), sq_nonneg (a - 2 * b - (a - 1)), 
          sq_nonneg (a - 1 - (1 - 2 * b)), h]