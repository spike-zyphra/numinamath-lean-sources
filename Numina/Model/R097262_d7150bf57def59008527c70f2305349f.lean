import Mathlib

theorem algebra_552
    (a b c : ℝ)
    (h : a * c - b * c + c ^ 2 < 0) : b ^ 2 > 4 * a * c := by
  nlinarith [sq_nonneg (b - 2 * c), sq_nonneg (a - c), sq_nonneg (b - a - c), sq_nonneg (b - a + c), sq_nonneg (b + c - a), sq_nonneg (b + c - a)]