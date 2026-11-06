import Mathlib

theorem algebra_1574 {n : ℝ} (h : (n - 1994) ^ 2 + (1995 - n) ^ 2 = 1) :
    (1995 - n) * (n - 1994) = 0 := by
  nlinarith [sq_nonneg (n - 1994), sq_nonneg (1995 - n), sq_nonneg (n - 1994.5), sq_nonneg ((1995 : ℝ) - 1994.5)]