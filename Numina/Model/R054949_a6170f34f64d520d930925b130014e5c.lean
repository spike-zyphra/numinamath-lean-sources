import Mathlib

theorem algebra_7178 (x : ℝ) (hx : x > 0) (h : x ^ 6 - 8 * x ^ 4 - 8 * x ^ 2 - 9 = 0) :
    x = 3 := by
  have h1 : (x ^ 2) ^ 3 - 8 * (x ^ 2) ^ 2 - 8 * (x ^ 2) - 9 = 0 := by
    ring_nf at h ⊢
    linarith
  have h2 : (x^2 - 9) * (x^4 + x^2 + 1) = 0 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 9), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 4), sq_nonneg (x ^ 2 * (x ^ 2 - 1)), sq_nonneg (x ^ 2 - 3), sq_nonneg (x ^ 2 * (x ^ 2)), sq_nonneg (x), sq_pos_of_pos hx]
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Case where x^2 - 9 = 0, which implies x^2 = 9, so x = 3
    have h5 : x ^ 2 = 9 := by linarith
    nlinarith
  · -- For x^4 + x^2 + 1 = 0, we need to show that it's impossible for x > 0
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 4), sq_pos_of_pos hx, sq_nonneg (x ^ 4 * (x ^ 4)), sq_nonneg (x ^ 2 * (x ^ 2 - 1)), sq_nonneg (x ^ 2 - 3), sq_nonneg (x ^ 2 - 1)]