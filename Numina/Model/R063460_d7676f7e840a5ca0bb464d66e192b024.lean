import Mathlib

theorem algebra_321294 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : (6 : ℝ)^a = 2010) (h2 : (335 : ℝ)^b = 2010) :
    1 / a + 1 / b = 1 := by

  have ha1 : a ≠ 0 := by linarith
  have hb1 : b ≠ 0 := by linarith

  have h3 : a = Real.logb 6 2010 := by
    rw [← h1]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  have h4 : b = Real.logb 335 2010 := by
    rw [← h2]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith

  have ha2 : 1 / a = Real.logb 2010 6 := by
    rw [h3]
    field_simp [Real.logb]
    all_goals linarith
  have hb2 : 1 / b = Real.logb 2010 335 := by
    rw [h4]
    field_simp [Real.logb]
    all_goals linarith

  rw [ha2, hb2]

  have h5 : Real.logb 2010 6 + Real.logb 2010 335 = Real.logb 2010 (6 * 335 : ℝ) := by
    rw [Real.logb_mul (by norm_num) (by norm_num)]
  rw [h5]
  norm_num [Real.logb_eq_iff_rpow_eq]
  all_goals linarith