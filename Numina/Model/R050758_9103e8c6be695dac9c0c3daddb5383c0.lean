import Mathlib

theorem algebra_223424 {x y : ℝ}
    (hx : (x - 1)^3 + 2003 * (x - 1) = -1) (hy : (y - 1)^3 + 2003 * (y - 1) = 1) :
    x + y = 2 := by
  have h : (x - 1) ^ 3 + 2003 * (x - 1) + (y - 1) ^ 3 + 2003 * (y - 1) = 0 := by
    linarith
  have h2 : (x + y - 2) * ((x + y - 2) ^ 2 - 3 * (x - 1) * (y - 1) + 2003) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
      sq_nonneg (x + y - 2), sq_nonneg ((x - 1) - (y - 1))]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · 
    linarith
  · 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
      sq_nonneg (x + y - 2), sq_nonneg ((x - 1) - (y - 1))]