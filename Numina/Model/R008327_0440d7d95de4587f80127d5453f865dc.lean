import Mathlib


theorem algebra_12716 (x k: ℝ) (hx : Real.logb 4 3 = x) (hk : Real.logb 2 27 = k * x) :
  k = 6 := by
  have h1 : x = Real.logb 2 3 / 2 := by
    have h2 : Real.logb 4 3 = Real.logb 2 3 / 2 := by
      have h4 : Real.logb 4 3 = Real.logb 2 3 / Real.logb 2 4 := by
        field_simp [Real.logb]
      have h5 : Real.logb 2 4 = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      rw [h5] at h4
      exact h4
    linarith [hx, h2]
  
  have h3 : Real.logb 2 27 = 3 * Real.logb 2 3 := by
    have h4 : Real.logb 2 27 = Real.logb 2 (3 ^ 3) := by norm_num
    rw [h4]
    simp [Real.logb_pow]
    all_goals linarith
  
  rw [h3] at hk
  rw [h1] at hk
  
  have h4 : Real.logb 2 3 ≠ 0 := by
    apply ne_of_gt
    apply Real.logb_pos
    all_goals norm_num
  
  have h5 : 3 * Real.logb 2 3 = k * (Real.logb 2 3 / 2) := by 
    linarith
  
  have h6 : 3 = k / 2 := by 
    apply (mul_left_inj' h4).mp
    linarith
  
  linarith