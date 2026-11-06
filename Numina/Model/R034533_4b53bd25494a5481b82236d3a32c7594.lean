import Mathlib

theorem algebra_15734 {x : ℝ} (hx : x ≠ 0) (h : 23 = x ^ 4 + 1 / x ^ 4) :
    x ^ 2 + 1 / x ^ 2 = 5 := by
  have h1 : (x ^ 2 + 1 / x ^ 2) ^ 2 = 25 := by 
    have h2 : x ^ 4 + 1 / x ^ 4 = 23 := by 
      linarith
    calc 
      (x ^ 2 + 1 / x ^ 2) ^ 2 = x ^ 4 + 1 / x ^ 4 + 2 := by 
        field_simp 
        ring 
      _ = 23 + 2 := by 
        rw [h2] 
      _ = (25 : ℝ) := by 
        norm_num
  have h2 : x ^ 2 + 1 / x ^ 2 > 0 := by 
    have hx1 : x ^ 2 > 0 := by 
      have hx2 : x ≠ 0 := hx 
      exact sq_pos_of_ne_zero hx2 
    have hx2 : 1 / x ^ 2 > 0 := by 
      apply div_pos 
      norm_num 
      have hx3 : x ^ 2 > 0 := hx1 
      linarith
    linarith
  have h3 : x ^ 2 + 1 / x ^ 2 = 5 := by 
    nlinarith [h1, h2]
  linarith [h3]