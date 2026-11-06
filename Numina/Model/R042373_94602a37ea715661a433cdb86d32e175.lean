import Mathlib

theorem algebra_206019 : (6 - Real.logb 14 2401) / (4 - Real.logb 14 49) = Real.logb 28 56 := by

  have h1 : Real.logb 14 2401 = 4 * Real.logb 14 7 := by
    rw [show (2401 : ℝ) = 7 ^ 4 by norm_num]
    simp [Real.logb_pow]

  have h2 : Real.logb 14 49 = 2 * Real.logb 14 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num]
    simp [Real.logb_pow]

  have h3 : Real.logb 28 56 = Real.logb 14 56 / Real.logb 14 28 := by
    field_simp [Real.logb]

  have h4 : Real.logb 14 56 = Real.logb 14 4 + 1 := by
    have h5 : Real.logb 14 56 = Real.logb 14 (4 * 14) := by
      norm_num
    rw [h5]
    have h6 : Real.logb 14 (4 * 14) = Real.logb 14 4 + Real.logb 14 14 := by
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    rw [h6]
    have h7 : Real.logb 14 14 = 1 := Real.logb_self_eq_one (by norm_num)
    rw [h7]

  have h8 : Real.logb 14 28 = Real.logb 14 2 + 1 := by
    have h9 : Real.logb 14 28 = Real.logb 14 (2 * 14) := by
      norm_num
    rw [h9]
    have h10 : Real.logb 14 (2 * 14) = Real.logb 14 2 + Real.logb 14 14 := by
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    rw [h10]
    have h11 : Real.logb 14 14 = 1 := Real.logb_self_eq_one (by norm_num)
    rw [h11]

  have h12 : Real.logb 14 4 = 2 * Real.logb 14 2 := by
    have h13 : Real.logb 14 4 = Real.logb 14 (2 ^ 2) := by
      norm_num
    rw [h13]
    simp [Real.logb_pow]

  have h14 : Real.logb 14 2 = 1 - Real.logb 14 7 := by
    have h15 : Real.logb 14 2 + Real.logb 14 7 = 1 := by
      have h16 : Real.logb 14 2 + Real.logb 14 7 = Real.logb 14 (2 * 7) := by
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      rw [h16]
      have h17 : Real.logb 14 (2 * 7) = Real.logb 14 14 := by
        norm_num
      rw [h17]
      have h18 : Real.logb 14 14 = 1 := Real.logb_self_eq_one (by norm_num)
      rw [h18]
    linarith

  have h19 : Real.logb 14 4 = 2 - 2 * Real.logb 14 7 := by
    have h20 : Real.logb 14 4 = 2 * Real.logb 14 2 := h12
    rw [h20, h14]
    ring

  have h21 : Real.logb 14 28 = 2 - Real.logb 14 7 := by
    have h22 : Real.logb 14 28 = Real.logb 14 2 + 1 := h8
    rw [h22, h14]
    ring

  have h23 : Real.logb 14 56 = 3 - 2 * Real.logb 14 7 := by
    linarith [h4, h19]

  have h24 : Real.logb 14 28 = 2 - Real.logb 14 7 := h21

  rw [h1, h2, h3, h23, h24]

  have h25 : (6 - 4 * Real.logb 14 7) / (4 - 2 * Real.logb 14 7) = (3 - 2 * Real.logb 14 7) / (2 - Real.logb 14 7) := by
    have h28 : (2 : ℝ) ≠ 0 := by norm_num
    have h26 : (6 - 4 * Real.logb 14 7) = 2 * (3 - 2 * Real.logb 14 7) := by ring
    have h27 : (4 - 2 * Real.logb 14 7) = 2 * (2 - Real.logb 14 7) := by ring
    rw [h26, h27]
    have h29 : 2 - Real.logb 14 7 ≠ 0 := by
      by_contra h
      have h34 : Real.logb 14 7 = 2 := by linarith
      have h35 : (14 : ℝ) ^ (2 : ℝ) = (7 : ℝ) := by
        rw [← h34]
        field_simp [Real.rpow_logb]
      norm_num at h35
    field_simp [h29]
    all_goals ring

  rw [h25]