import Mathlib

theorem algebra_12946 (a b : ℝ) (ha : a^2 - 18 * a = b) (hb : b < 0) :
    (1 / 2) * 18 * (-b) ≤ 729 := by 
  nlinarith [sq_nonneg (a - 9)]