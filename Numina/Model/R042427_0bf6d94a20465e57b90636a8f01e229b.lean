import Mathlib

theorem algebra_305789 (x : ℝ) (hx : x > 0) (h : 17 * x^19 - 4 * x^17 - 17 * x^15 + 4 = 0) :
    x = 1 := by
  have h1 : x ^ 15 * (17 * x ^ 4 - 4 * x ^ 2 - 17) + 4 = 0 := by
    ring_nf at h ⊢
    linarith
  have h2 : (x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 8 - 1), 
        sq_nonneg (x ^ 16 - 1), sq_nonneg (x ^ 9 - x ^ 5), sq_nonneg (x ^ 7 - x ^ 3), 
        sq_nonneg (x ^ 4 - x ^ 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), 
        mul_pos hx hx, mul_pos hx (show x ^ 2 > 0 by positivity), 
        mul_pos hx (show x ^ 4 > 0 by positivity), 
        mul_pos hx (show x ^ 14 > 0 by positivity)]
  have h3 : x - 1 = 0 := by
    apply pow_eq_zero 
    exact h2
  have h4 : x = 1 := by
    linarith 
  exact h4