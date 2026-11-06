import Mathlib

theorem inequalities_180261 (x y : ℝ) (h : 2 * y + 5 * x = 10) :
    3 * x * y - x ^ 2 - y ^ 2 < 7 := by
  have h1 : y = 5 - 5 / 2 * x := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (x - 80 / 59), sq_nonneg (x - 20 / 59), sq_nonneg (x - 40 / 59)]