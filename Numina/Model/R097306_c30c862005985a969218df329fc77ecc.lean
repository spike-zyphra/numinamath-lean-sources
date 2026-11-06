import Mathlib

theorem algebra_304302 {a b c : ℝ} (h1 : a + b + c = 0) (h2 : a^2 + b^2 + c^2 = 4) :
    a^4 + b^4 + c^4 = 8 := by 
  have h3 : a * b + a * c + b * c = -2 := by
    have h3 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by
      ring
    rw [h1, h2] at h3
    linarith

  have h4 : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 = 4 := by 
    have h4 : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 = (a * b + a * c + b * c) ^ 2 - 2 * (a * b * c) * (a + b + c) := by 
      ring
    rw [h4, h3, h1]
    norm_num
  
  have h5 : a^4 + b^4 + c^4 = (a^2 + b^2 + c^2) ^ 2 - 2 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) := by 
    ring
  
  rw [h5, h2, h4]
  norm_num
  <;> nlinarith [h1, h2, h3]