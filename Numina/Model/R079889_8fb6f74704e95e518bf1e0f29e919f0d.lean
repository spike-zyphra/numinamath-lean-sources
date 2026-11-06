import Mathlib

theorem algebra_134666 (x : ℝ) (hx : x^4 - 3 * x^3 + 4 * x^2 - 3 * x + 1 = 0) :
    x = 1 := by
  have h1 : (x - 1)^2 * (x^2 - x + 1) = 0 := by 
    nlinarith [sq_nonneg (x^2 - x), sq_nonneg (x - 1)]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · 
    have h4 : x - 1 = 0 := by 
      apply pow_eq_zero 
      exact h2
    linarith 
  · 
    have h4 : x^2 - x + 1 = 0 := h3
    have h5 : x^2 - x + 1 > 0 := by 
      nlinarith [sq_nonneg (x - 0.5)]
    nlinarith