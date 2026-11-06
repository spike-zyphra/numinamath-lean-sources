import Mathlib

theorem algebra_216174 {x y : ℝ} (h1 : x + y = 1) (h2 : x^3 + y^3 = 13) :
    x^2 + y^2 = 9 := by 
  have h3 : x * y = -4 := by
    have h3_id : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by 
      ring 
    rw [h1] at h3_id 
    rw [h2] at h3_id 
    linarith 
  have h4 : x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by 
    ring 
  rw [h1, h3] at h4 
  linarith