import Mathlib

theorem algebra_129607 {a b : ℝ} (ha : a^3 = 3 * a * b^2 + 11) (hb : b^3 = 3 * a^2 * b + 2) :
    a^2 + b^2 = 5 := by 
  have h1 : a^3 + b^3 = 3 * a * b^2 + 11 + (3 * a^2 * b + 2) := by 
    linarith [ha, hb]
  have h2 : a^3 - b^3 = (3 * a * b^2 + 11) - (3 * a^2 * b + 2) := by 
    linarith [ha, hb]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - b^2), sq_nonneg (a*b), sq_nonneg (a^2 + b^2 - 5), h1, h2]