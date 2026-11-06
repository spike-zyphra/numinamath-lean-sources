import Mathlib

theorem algebra_14503 {x : ℝ} (hx : x > -4) (h : Real.logb 5 (x + 4) = 3) :
    Real.logb 11 x = 2 := by 
  have h5 : x + 4 > 0 := by linarith [hx]
  have h6 : x + 4 = (5 : ℝ) ^ (3 : ℝ) := by 
    rw [Real.logb_eq_iff_rpow_eq] at h 
    all_goals linarith [h5]
  have hx_eq : x = 121 := by 
    have h7 : x + 4 = (125 : ℝ) := by 
      norm_num at h6 ⊢
      exact_mod_cast h6
    linarith
  rw [hx_eq]
  have h7 : Real.logb 11 (121 : ℝ) = 2 := by 
    rw [Real.logb_eq_iff_rpow_eq] 
    all_goals norm_num
  linarith [h7]