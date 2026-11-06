import Mathlib

theorem algebra_195540 (x : ℝ) (hx : 2*x^3-5*x^2+6*x-2=0) (hx' : 6*x^3-3*x^2-2*x+1=0) :
    x=1/2 ∨ x=1/Real.sqrt 3 ∨ x=2/Real.sqrt 3 := by
  have eq1 : 12*x^2 - 20*x + 7 = 0 := by
    nlinarith [hx, hx']
  have h2 : (x - 1/2) * (x - 7/6) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Case where x = 1/2
    left
    linarith
  · -- Case where x = 7/6
    nlinarith [sq_nonneg (x^2), sq_nonneg ((x - 1/2) ^ 2), sq_nonneg (x^2 - 1), sq_nonneg (x^2 - 1/4), sq_nonneg (x * (x - 1))]