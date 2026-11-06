import Mathlib

theorem algebra_152950 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x^2 + y^2 = 1) (h2 : x^4 + y^4 = 17 / 18) :
    x * y = 1 / 6 := by
  have h3 : x^4 + y^4 = (x^2 + y^2)^2 - 2 * (x * y)^2 := by
    ring
  rw [h1] at h3
  rw [h2] at h3
  have h4 : 2 * (x * y)^2 = 1 - 17 / 18 := by 
    linarith 
  have h5 : (x * y)^2 = 1 / 36 := by 
    nlinarith
  have h6 : x * y > 0 := by 
    apply mul_pos 
    exact hx 
    exact hy 
  have h7 : x * y = 1 / 6 := by 
    nlinarith [h5, h6] 
  exact h7