import Mathlib

theorem algebra_11933 {x : ℝ} (hx : x > 0) (h : Real.logb 2 x = Real.logb 4 (2 * x) + Real.logb 8 (4 * x)) :
    x = 128 := by

  have h1 : Real.logb 4 (2 * x) = (Real.logb 2 (2 * x)) / (Real.logb 2 (4 : ℝ)) := by
    field_simp [Real.logb]

  have h2 : Real.logb 2 (2 * x) = Real.logb 2 (2 : ℝ) + Real.logb 2 x := by
    rw [Real.logb_mul (by norm_num) (by linarith)]

  have h3 : Real.logb 2 (2 : ℝ) = 1 := by
    norm_num [Real.logb_self_eq_one]

  have h4 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num

  have h5 : Real.logb 4 (2 * x) = (1 + Real.logb 2 x) / 2 := by
    rw [h1]
    have h6 : Real.logb 2 (2 * x) = 1 + Real.logb 2 x := by
      rw [h2, h3]
    rw [h6]
    have h7 : Real.logb 2 (4 : ℝ) = 2 := h4
    rw [h7]
    all_goals linarith

  have h8 : Real.logb 8 (4 * x) = (2 + Real.logb 2 x) / 3 := by
    have h9 : Real.logb 8 (4 * x) = (Real.logb 2 (4 * x)) / (Real.logb 2 (8 : ℝ)) := by 
      field_simp [Real.logb]

    have h10 : Real.logb 2 (4 * x) = Real.logb 2 (4 : ℝ) + Real.logb 2 x := by 
      rw [Real.logb_mul (by norm_num) (by linarith)]

    have h11 : Real.logb 2 (4 : ℝ) = 2 := h4

    have h12 : Real.logb 2 (4 * x) = 2 + Real.logb 2 x := by 
      rw [h10, h11]

    have h13 : Real.logb 2 (8 : ℝ) = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num

    rw [h9, h12, h13]

  rw [h5, h8] at h

  have h6 : Real.logb 2 x = 7 := by
    linarith

  have h7 : x = (2 : ℝ) ^ (7 : ℝ) := by 
    have h8 : x = (2 : ℝ) ^ (Real.logb 2 x) := by 
      field_simp
    rw [h8, h6]

  rw [h7]
  norm_num