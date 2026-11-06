import Mathlib

theorem algebra_305081 (a b : ℝ) (h : 3*a^2-10*a*b+8*b^2+5*a-10*b=0) :
    9*a^2+72*b+2 ≥ -34 := by
  have h2 : (a - 2 * b) * (a - (4 * b - 5) / 3) = 0 := by
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - (4 * b - 5) / 3), sq_nonneg (a * 3 - 1 * (4 * b - 5)), sq_nonneg (b - (-1)), sq_nonneg (a + 2), sq_nonneg (a + 3), sq_nonneg (b - (-1))]
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Case a = 2b
    have ha : a = 2 * b := by linarith [h3]
    rw [ha]
    nlinarith [sq_nonneg (b + 1), sq_nonneg ((b + 1) * 6), sq_nonneg ((2 * b + 2) * (b + 1))]
  · -- Case a = (4b -5)/3
    have ha : a = (4 * b - 5) / 3 := by linarith [h4]
    rw [ha]
    nlinarith [sq_nonneg (b + 1), sq_nonneg ((4 * b - 5) / 3 * 6), sq_nonneg ((b + 1) * 8), sq_nonneg ((b + 1) * 6)]