import Mathlib

theorem algebra_16353 {x y : ℚ} (hy : y ≠ 0) (h : (x + 5) / (y + 5) = 1 / 2) (hx : x = 2) :
    y = 9 := by
  rw [hx] at h 
  have h1 : (2 + 5 : ℚ) / (y + 5) = 1 / 2 := h
  have h2 : (2 + 5 : ℚ) * 2 = (y + 5) * 1 := by 
    field_simp [(show (y + 5 : ℚ) ≠ 0 by 
      by_contra h'
      rw [h'] at h1
      norm_num at h1
      )] at h1
    linarith 
  norm_num at h2 
  linarith