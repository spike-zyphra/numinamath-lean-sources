import Mathlib

theorem algebra_19751 (x y : ℝ) (h : midpoint ℝ (x, y) (2, 4) = (-7, 0)) :
    (x, y) = (-16, -4) := by 
  simp [midpoint_eq_smul_add, Prod.ext_iff] at h 
  have hx1 : x = -16 := by 
    linarith 
  have hy1 : y = -4 := by 
    linarith 
  simp [Prod.ext_iff, hx1, hy1] 
  all_goals norm_num