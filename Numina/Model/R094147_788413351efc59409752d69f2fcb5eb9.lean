import Mathlib

theorem algebra_198561 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h₁ : (2 : ℝ)^x = 196) (h₂ : (7 : ℝ)^y = 196) :
    1 / x + 1 / y = 1 / 2 := by
  have hx_eq : x = Real.logb 2 196 := by 
    rw [← h₁]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith 
  have hy_eq : y = Real.logb 7 196 := by 
    rw [← h₂]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith 
  have h3 : 1 / x = Real.log 2 / Real.log 196 := by 
    rw [hx_eq]
    have h4 : Real.logb 2 196 = Real.log 196 / Real.log 2 := by 
      field_simp [Real.logb]
    rw [h4]
    field_simp
    <;> ring_nf 
    <;> field_simp [Real.logb]
    all_goals linarith 
  have h4 : 1 / y = Real.log 7 / Real.log 196 := by 
    rw [hy_eq]
    have h5 : Real.logb 7 196 = Real.log 196 / Real.log 7 := by 
      field_simp [Real.logb]
    rw [h5]
    field_simp
    <;> ring_nf 
    <;> field_simp [Real.logb]
    all_goals linarith 
  have h5 : 1 / x + 1 / y = (Real.log 2 + Real.log 7) / Real.log 196 := by 
    rw [h3, h4]
    ring 
  have h6 : Real.log 2 + Real.log 7 = Real.log 14 := by 
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    all_goals norm_num 
  have h7 : Real.log 196 = 2 * Real.log 14 := by 
    calc 
      Real.log 196 = Real.log (14 ^ 2) := by norm_num 
      _ = 2 * Real.log 14 := by 
        simp [Real.log_pow]
        all_goals norm_num 
  rw [h5, h6, h7]
  have h8 : Real.log 14 > 0 := by
    apply Real.log_pos
    all_goals norm_num 
  have h9 : Real.log 14 ≠ 0 := by 
    linarith 
  field_simp [h9]
  <;> ring_nf 
  <;> field_simp [h9]
  all_goals linarith 
  all_goals norm_num 
  all_goals linarith 
  all_goals norm_num 
  all_goals linarith 
  all_goals norm_num 
  all_goals linarith 
  all_goals norm_num