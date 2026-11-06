import Mathlib

theorem algebra_3622 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 7) :
    x ^ 4 + 1 / x ^ 4 = 2207 := by
  have h1 : x ^ 2 + 1 / x ^ 2 = 47 := by
    have h2 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by 
      field_simp [hx]
      ring
    rw [h2, h]
    norm_num
  
  have h3 : x ^ 4 + 1 / x ^ 4 = (x ^ 2 + 1 / x ^ 2) ^ 2 - 2 := by 
    field_simp [hx]
    ring
  
  rw [h3, h1]
  norm_num