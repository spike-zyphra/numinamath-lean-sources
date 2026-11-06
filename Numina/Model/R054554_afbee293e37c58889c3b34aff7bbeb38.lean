import Mathlib

theorem algebra_322828 {x y : ℝ} (h1 : x + y = 3) (h2 : x^2 + y^2 - x * y = 4) :
    x^4 + y^4 + x^3 * y + x * y^3 = 36 := by
  have h3 : x * y = 5 / 3 := by
    have h4 : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    rw [h1] at h4
    nlinarith
  have h4 : x^2 + y^2 = 17 / 3 := by
    have h5 : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    rw [h1, h3] at h5
    linarith 
  have h5 : x^4 + y^4 = (x^2 + y^2) ^ 2 - 2 * (x * y) ^ 2 := by ring
  have h6 : x^3 * y + x * y^3 = (x * y) * (x^2 + y^2) := by ring 
  calc
    x^4 + y^4 + x^3 * y + x * y^3
        = (x^4 + y^4) + (x^3 * y + x * y^3) := by ring
    _ = ((x^2 + y^2) ^ 2 - 2 * (x * y) ^ 2) + ((x * y) * (x^2 + y^2)) := by rw [h5, h6]
    _ = ((17 / 3) ^ 2 - 2 * (5 / 3) ^ 2) + ((5 / 3) * (17 / 3)) := by 
      rw [h4, h3]
    _ = 36 := by norm_num