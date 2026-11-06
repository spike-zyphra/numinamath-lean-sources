import Mathlib

theorem algebra_168700 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h₁ : (75 : ℝ)^x = 10^(-2 : ℤ)) (h₂ : (0.75 : ℝ)^y = 10^(-2 : ℤ)) :
    1 / x - 1 / y = -1 := by

  have eq1 : x * (Real.logb 10 (75 : ℝ)) = -2 := by
    have h1' : (75 : ℝ) ^ x = (10 : ℝ) ^ (-2 : ℝ) := by
      rw [h₁]
      norm_num
    have h3 : Real.logb 10 ((75 : ℝ) ^ x) = Real.logb 10 ((10 : ℝ) ^ (-2 : ℝ)) := by
      rw [h1']
    have h4 : Real.logb 10 ((75 : ℝ) ^ x) = x * Real.logb 10 (75 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    have h5 : Real.logb 10 ((10 : ℝ) ^ (-2 : ℝ)) = (-2 : ℝ) * Real.logb 10 (10 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    rw [h4, h5] at h3
    have h6 : Real.logb 10 (10 : ℝ) = 1 := by
      rw [Real.logb_self_eq_one]
      all_goals norm_num
    rw [h6] at h3
    linarith
  have eq2 : y * (Real.logb 10 (0.75 : ℝ)) = -2 := by
    have h2' : (0.75 : ℝ) ^ y = (10 : ℝ) ^ (-2 : ℝ) := by
      rw [h₂]
      norm_num
    have h3 : Real.logb 10 ((0.75 : ℝ) ^ y) = Real.logb 10 ((10 : ℝ) ^ (-2 : ℝ)) := by
      rw [h2']
    have h4 : Real.logb 10 ((0.75 : ℝ) ^ y) = y * Real.logb 10 (0.75 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    have h5 : Real.logb 10 ((10 : ℝ) ^ (-2 : ℝ)) = (-2 : ℝ) * Real.logb 10 (10 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    rw [h4, h5] at h3
    have h6 : Real.logb 10 (10 : ℝ) = 1 := by
      rw [Real.logb_self_eq_one]
      all_goals norm_num
    rw [h6] at h3
    linarith
  have eq3 : 1 / x = Real.logb 10 (75 : ℝ) / (-2 : ℝ) := by
    have h5 : Real.logb 10 (75 : ℝ) ≠ 0 := by
      have : Real.logb 10 (75 : ℝ) > 0 := by
        apply Real.logb_pos
        all_goals norm_num
      linarith
    field_simp at *
    nlinarith [eq1, h5]
  have eq4 : 1 / y = Real.logb 10 (0.75 : ℝ) / (-2 : ℝ) := by
    have h6 : Real.logb 10 (0.75 : ℝ) ≠ 0 := by
      have : Real.logb 10 (0.75 : ℝ) < 0 := by
        have : (0.75 : ℝ) < 1 := by norm_num
        have h1 : Real.logb 10 (0.75 : ℝ) < Real.logb 10 (1 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals norm_num
        have h2 : Real.logb 10 (1 : ℝ) = 0 := Real.logb_one
        linarith [h1, h2]
      linarith
    field_simp at *
    nlinarith [eq2, h6]
  rw [eq3, eq4]
  have h7 : Real.logb 10 (75 : ℝ) - Real.logb 10 (0.75 : ℝ) = 2 := by
    have h8 : Real.logb 10 (75 : ℝ) - Real.logb 10 (0.75 : ℝ) = Real.logb 10 ((75 : ℝ) / (0.75 : ℝ)) := by
      rw [Real.logb_div (by norm_num) (by norm_num)]
    rw [h8]
    have h9 : (75 : ℝ) / (0.75 : ℝ) = (100 : ℝ) := by
      norm_num
    rw [h9]
    have h10 : Real.logb 10 (100 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith [h10]
  have h8 : Real.logb 10 (75 : ℝ) / (-2 : ℝ) - Real.logb 10 (0.75 : ℝ) / (-2 : ℝ) = -1 := by
    have h9 : Real.logb 10 (75 : ℝ) - Real.logb 10 (0.75 : ℝ) = 2 := h7
    have h10 : Real.logb 10 (75 : ℝ) / (-2 : ℝ) - Real.logb 10 (0.75 : ℝ) / (-2 : ℝ) = (Real.logb 10 (75 : ℝ) - Real.logb 10 (0.75 : ℝ)) / (-2 : ℝ) := by
      ring
    rw [h10, h9]
    all_goals norm_num
  linarith [h8]