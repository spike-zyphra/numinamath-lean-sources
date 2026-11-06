import Mathlib

theorem algebra_8155 (x : ℝ) (h : x ≠ -2013) (h' : 4/3 + 4*(1/2013 + 1/x) = 12) :
    2010 + 8*(2013*x/(2013 + x)) = 2013 := by
  have hx1 : x ≠ 0 := by
    by_contra hx
    rw [hx] at h'
    norm_num at h'
  
  have hx2 : 2013 + x ≠ 0 := by
    intro h_eq
    have : x = -2013 := by linarith
    tauto
  
  have eq1 : 1/2013 + 1/x = 8/3 := by
    have eq2 : 4/3 + 4*(1/2013 + 1/x) = 12 := h'
    linarith [eq2]

  have eq2 : 3 * (x + 2013) = 8 * 2013 * x := by
    have eq3 : 1/2013 + 1/x = 8/3 := eq1
    field_simp [hx1, show 2013 ≠ 0 by norm_num] at eq3 ⊢
    nlinarith [eq3]
  
  have eq3 : 2013 * x / (2013 + x) = 3 / 8 := by
    have hx5 : 2013 + x ≠ 0 := hx2
    field_simp [hx5] at eq2 ⊢
    nlinarith

  have hx7 : 8 * (2013 * x / (2013 + x)) = 3 := by
    rw [eq3]
    norm_num
  
  linarith [hx7]