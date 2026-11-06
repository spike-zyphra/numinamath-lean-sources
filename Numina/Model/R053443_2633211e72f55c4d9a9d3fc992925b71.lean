import Mathlib

theorem algebra_249741 {a b : ℝ} (ha : Real.logb 14 7 = a) (hb : Real.logb 14 5 = b) :
    Real.logb 35 28 = (2 - a) / (b + a) := by
  have h1 : Real.logb 35 28 = Real.logb 14 28 / Real.logb 14 35 := by
    field_simp [Real.logb]
    all_goals linarith
  have h2 : Real.logb 14 28 = 2 - a := by
    have h_14_14 : Real.logb 14 14 = 1 := Real.logb_self_eq_one (by norm_num)
    have h_14_28 : Real.logb 14 28 = Real.logb 14 14 + Real.logb 14 2 := by
      rw [show (28 : ℝ) = 14 * 2 by norm_num]
      exact Real.logb_mul (by norm_num) (by norm_num)
    have h_14_2 : Real.logb 14 2 = 1 - a := by
      have h_2 : Real.logb 14 2 = Real.logb 14 14 - Real.logb 14 7 := by
        rw [← Real.logb_div (by norm_num) (by norm_num)]
        norm_num
      rw [h_2]
      rw [show Real.logb 14 14 = 1 by apply Real.logb_self_eq_one; all_goals norm_num]
      rw [show Real.logb 14 7 = a by linarith [ha]]
      all_goals linarith
    rw [h_14_14, h_14_2] at h_14_28
    linarith
  have h3 : Real.logb 14 35 = b + a := by
    have h_14_35 : Real.logb 14 35 = Real.logb 14 5 + Real.logb 14 7 := by 
      rw [show (35 : ℝ) = 5 * 7 by norm_num]
      exact Real.logb_mul (by norm_num) (by norm_num)
    rw [show Real.logb 14 5 = b by linarith [hb], show Real.logb 14 7 = a by linarith [ha]] at h_14_35
    linarith
  rw [h1]
  rw [h2, h3]
  all_goals linarith