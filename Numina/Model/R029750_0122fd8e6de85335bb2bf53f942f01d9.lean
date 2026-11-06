import Mathlib

theorem algebra_317779 (a b c d : ℝ) (ha : a^4 + b^4 = 2011) (hb : c^4 + d^4 = 2011) (hc : a * c + b * d = 0) :
    a * b + c * d = 0 := by
  have h1 : (a * c + b * d) ^ 2 = 0 := by 
    rw [hc]
    norm_num
  have h2 : a^2 * c^2 + b^2 * d^2 = -2 * a * b * c * d := by
    nlinarith
  have h3 : (a * b + c * d) ^ 2 = a^2 * b^2 + c^2 * d^2 + 2 * a * b * c * d := by
    ring
  nlinarith [sq_nonneg (a^2 - d^2), sq_nonneg (b^2 - c^2), sq_nonneg (a * d - b * c), sq_nonneg (a * b * c * d), sq_nonneg (a * c), sq_nonneg (b * d), sq_nonneg (a * b), sq_nonneg (c * d), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c)]