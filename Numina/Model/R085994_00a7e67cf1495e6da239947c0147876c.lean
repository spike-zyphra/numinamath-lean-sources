import Mathlib

theorem algebra_193726 {a b : ℝ} (ha : a > 0) (h : a^2 - 1 = 123 * 125) :
    a = 124 := by
  have h1 : a^2 = 15376 := by
    nlinarith
  have h3 : a^2 - (124 : ℝ) ^ 2 = 0 := by 
    nlinarith [h1]
  have h4 : (a - (124 : ℝ)) * (a + (124 : ℝ)) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · linarith
  · nlinarith