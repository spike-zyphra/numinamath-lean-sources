import Mathlib

theorem algebra_292442 {x y : ℝ} (h : x^2 + y^2 = 1) :
    x^6 + 3 * x^2 * y^2 + y^6 = 1 := by
  have h1 : x^6 + y^6 = (x^2 + y^2)^3 - 3 * x^2 * y^2 * (x^2 + y^2) := by 
    ring_nf
  have h2 : x^6 + y^6 = 1 - 3 * x^2 * y^2 := by
    rw [h] at h1
    linarith
  have h3 : x^6 + 3 * x^2 * y^2 + y^6 = (x^6 + y^6) + 3 * x^2 * y^2 := by 
    ring
  rw [h3]
  rw [h2]
  all_goals linarith