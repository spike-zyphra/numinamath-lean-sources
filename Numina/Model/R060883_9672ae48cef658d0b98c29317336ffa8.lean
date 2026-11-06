import Mathlib

theorem inequalities_208104 (x : ℝ) : x^4 > x - 1 / 2 := by
  nlinarith [sq_nonneg (x^2 - x / 2), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x ^ 2 - 1 / 2), sq_nonneg (x ^ 2 - x),
          sq_nonneg (x ^ 2 + x), sq_nonneg (x - 1), sq_nonneg (x + 1),
          sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x ^ 2 - x + 1 / 4), sq_nonneg ((x ^ 2 - 1 / 2)), sq_nonneg ((x + 1 / 2) - (x - 1 / 2))]