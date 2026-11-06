import Mathlib

theorem algebra_240315 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (65 / 100) * x + (45 / 100) * y = (53 / 100) * (x + y)) :
    x / (x + y) = 40 / 100 := by

  have h2 : 12 * x = 8 * y := by
    linarith
  
  have h3 : 3 * x = 2 * y := by 
    linarith
  
  have h4 : x = (2 / 3) * y := by 
    linarith
  
  have h5 : x + y ≠ 0 := by 
    linarith [hx, hy]

  have h6 : x / (x + y) = 2 / 5 := by 
    have hy' : y ≠ 0 := by linarith
    have h7 : x + y = (5 / 3) * y := by 
      rw [h4]
      linarith 
    have h8 : x = (2 / 3) * y := h4 
    rw [h7]
    rw [h8]
    field_simp [hy']
    <;> linarith
  
  rw [h6]
  norm_num