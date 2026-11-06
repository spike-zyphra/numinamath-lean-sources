import Mathlib

theorem algebra_146512 (a b c : ℝ) (ha : a = Real.sqrt 2 + 1) (hb : b = 3 / (Real.sqrt 6 - Real.sqrt 3)) (hc : c = 3 * Real.sqrt 2 + 3) :
    b / a = Real.sqrt 3 := by 
  have hb' : b = Real.sqrt 6 + Real.sqrt 3 := by 
    rw [hb]
    have h3 : Real.sqrt 6 > 0 := by 
      apply Real.sqrt_pos.mpr 
      all_goals norm_num 
    have h4 : Real.sqrt 3 > 0 := by 
      apply Real.sqrt_pos.mpr 
      all_goals norm_num 
    have h5 : Real.sqrt 6 - Real.sqrt 3 ≠ 0 := by 
      have h6 : Real.sqrt 6 > Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith 
    field_simp [(show Real.sqrt 6 - Real.sqrt 3 ≠ 0 by assumption)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_pos_of_pos (show (0 : ℝ) < (6 : ℝ) by norm_num), sq_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (3 : ℝ) ≤ (6 : ℝ) by norm_num)]
  rw [hb', ha]
  have h1 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf <;> norm_num 
  rw [h1] 
  have h2 : Real.sqrt 2 > 0 := by 
    apply Real.sqrt_pos.mpr 
    all_goals norm_num 
  field_simp [(show Real.sqrt 2 + 1 ≠ 0 by 
    have h3 : Real.sqrt 2 > 0 := by apply Real.sqrt_pos.mpr; norm_num 
    linarith 
  )] 
  <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), mul_pos (Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)) (Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num))]