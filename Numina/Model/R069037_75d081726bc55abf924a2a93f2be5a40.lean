import Mathlib

theorem algebra_320555 {x y : ℝ} (hx : x^2 = 2 * x + 1) (hy : y^2 = 2 * y + 1)
    (hxy : x ≠ y) : x^6 + y^6 = 198 := by
  have h1 : x + y = 2 := by 
    have h2 : x^2 - y^2 = 2 * (x - y) := by 
      nlinarith
    have h3 : x^2 - y^2 = (x - y) * (x + y) := by 
      ring
    have h4 : (x - y) * (x + y) = 2 * (x - y) := by 
      linarith [h2, h3]
    have h5 : x - y ≠ 0 := by 
      exact sub_ne_zero.mpr hxy
    have h6 : x + y = 2 := by 
      apply (mul_left_inj' h5).mp 
      linarith
    linarith [h6]
  have h2 : x * y = -1 := by 
    nlinarith [hx, hy, h1]
  have h3 : x^2 + y^2 = 6 := by 
    nlinarith [hx, hy, h1]
  have h4 : x^3 + y^3 = 14 := by 
    have h14 : x^3 + y^3 = (x + y) * ((x^2 + y^2) - (x * y)) := by 
      ring 
    rw [h14, h1, h3, h2]
    norm_num 
  have h5 : x^4 + y^4 = 34 := by 
    have h51 : x^4 + y^4 = (x + y) * (x^3 + y^3) - (x * y) * (x^2 + y^2) := by 
      ring 
    rw [h51, h1, h4, h2, h3]
    norm_num 
  have h6 : x^5 + y^5 = 82 := by 
    have h61 : x^5 + y^5 = (x + y) * (x^4 + y^4) - (x * y) * (x^3 + y^3) := by 
      ring 
    rw [h61, h1, h5, h2, h4]
    norm_num 
  have h7 : x^6 + y^6 = 198 := by 
    have h71 : x^6 + y^6 = (x + y) * (x^5 + y^5) - (x * y) * (x^4 + y^4) := by 
      ring 
    rw [h71, h1, h6, h2, h5]
    norm_num 
  linarith [h7]