import Mathlib

theorem algebra_146949 {a b : ℝ} (ha : a^2 - 3*a*b + 2*b^2 + a - b = 0) (hb : a^2 - 2*a*b + b^2 - 5*a + 7*b = 0) :
    a*b - 12*a + 15*b = 0 := by
  have h3 : -a * b + b^2 + 6 * a - 8 * b = 0 := by 
    nlinarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2 * b), sq_nonneg (a + b - 15), sq_nonneg (b - 3), sq_nonneg (a - 3), sq_nonneg (b - 5)]