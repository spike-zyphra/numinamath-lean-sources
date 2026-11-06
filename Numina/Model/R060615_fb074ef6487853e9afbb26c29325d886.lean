import Mathlib

theorem algebra_2472 {x y : ℝ} (hy : y ≠ 0) (h : x / y = 3 / 2) (h1 : x + 3 * y = 27) :
    min x y = 6 := by 
  have h2 : x = 3 / 2 * y := by
    have h2 : x / y = 3 / 2 := h
    field_simp [hy] at h2 
    linarith
  
  have h3 : x = 3 / 2 * y := h2 
  rw [h3] at h1 
  have h4 : y = 6 := by 
    linarith
  
  have h5 : x = 9 := by
    rw [h4] at h3 
    linarith
  
  rw [h4, h5]
  norm_num