import Mathlib

theorem algebra_608252 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (hsq: x^2 + y^2 = 1) (hqq: x^4 + y^4 = 17/(18:ℝ)): (x*y=1/(6:ℝ)) := by 
  have h1 : (x^2 + y^2)^2 = 1 := by
    rw [hsq]
    norm_num
  have h2 : x^4 + y^4 = (x^2 + y^2)^2 - 2 * (x * y)^2 := by 
    ring
  rw [hqq, h1] at h2
  have h3 : 2 * (x * y)^2 = 1 / 18 := by 
    nlinarith
  have h4 : (x * y)^2 = 1 / 36 := by
    linarith
  have h5 : 0 ≤ x * y := by 
    apply mul_nonneg
    linarith
    linarith
  have h6 : x * y = 1 / 6 := by 
    nlinarith
  exact h6