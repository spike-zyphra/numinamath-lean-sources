import Mathlib

theorem inequalities_213008 (x : ℝ) :
    x^4 - x^3 + 3 * x^2 - 2 * x + 2 ≥ 0 := by
  nlinarith [sq_nonneg (x ^ 2 - x / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x * (x - 1 / 2)), sq_nonneg ((x - 1 / 2) * (x - 1 / 2 + 1 / 2)), sq_nonneg (x ^ 2 * (x - 1 / 2)), sq_nonneg ((x ^ 2 - 1 / 2) * (x - 1 / 2)), sq_nonneg (x ^ 2 - 2 * x), sq_nonneg ((x ^ 2 - 2 * x) + x ^ 2), sq_nonneg ((x ^ 2 - 2 * x) + 2 * x), sq_nonneg ((x ^ 2 - x / 2) * (x ^ 2 - x / 2) ), sq_nonneg ((x - 1 / 2) * (x - 1 / 2) ), sq_nonneg ((x - 1) * (x - 1) ), sq_nonneg ((x - 2) * (x - 2) ), sq_nonneg ((x ^ 2 - 1) * (x ^ 2 - 1) ) ]