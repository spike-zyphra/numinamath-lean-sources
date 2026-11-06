import Mathlib

theorem algebra_10365 (a b c d : ℝ) (ha : (5 : ℝ)^a = 3) (hb : (4 : ℝ)^b = 2)
    (hc : (3 : ℝ)^c = 4) (hd : (2 : ℝ)^d = 5) :
    (a * b * c * d)^2021 = 1 := by

  have ha2 : a = Real.logb 5 3 := by
    rw [←ha]
    field_simp [Real.logb_eq_iff_rpow_eq]
  have hb2 : b = Real.logb 4 2 := by
    rw [←hb]
    field_simp [Real.logb_eq_iff_rpow_eq]
  have hc2 : c = Real.logb 3 4 := by
    rw [←hc]
    field_simp [Real.logb_eq_iff_rpow_eq]
  have hd2 : d = Real.logb 2 5 := by
    rw [←hd]
    field_simp [Real.logb_eq_iff_rpow_eq]

  have h1 : a * b * c * d = 1 := by
    rw [ha2, hb2, hc2, hd2]
    have h2 : Real.logb 5 3 = Real.log 3 / Real.log 5 := by
      field_simp [Real.logb]
    have h3 : Real.logb 4 2 = Real.log 2 / Real.log 4 := by
      field_simp [Real.logb]
    have h4 : Real.logb 3 4 = Real.log 4 / Real.log 3 := by
      field_simp [Real.logb]
    have h5 : Real.logb 2 5 = Real.log 5 / Real.log 2 := by
      field_simp [Real.logb]
    rw [h2, h3, h4, h5]
    have h6 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      simp [Real.log_pow]
      all_goals linarith
    rw [h6]
    field_simp
    <;> ring_nf
    <;> norm_num

  rw [h1]
  all_goals norm_num