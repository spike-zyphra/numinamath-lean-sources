import Mathlib

theorem algebra_51175 (x : ℝ) (hx : x > 0) (h : (1 + 20 / 100) * (1 - 10 / 100) * (1 + 20 / 100) * 14400 = (1 + x / 100) ^ 3 * 6250) :
    x = 44 := by
  nlinarith [sq_nonneg ((1 + x / 100) ^ 2), sq_nonneg ((1 + x / 100) - 44 / 100), sq_nonneg ((1 + x / 100) - 1.44), sq_nonneg ((1 + x / 100) - 2 / 5), sq_nonneg ((1 + x / 100) - 3.84)]