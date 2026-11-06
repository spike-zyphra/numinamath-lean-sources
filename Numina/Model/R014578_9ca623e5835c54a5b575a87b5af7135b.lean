import Mathlib

theorem algebra_13591 (x : ℝ) (hx : x > 0) :
    Real.logb 3 (x ^ (Real.logb 3 36)) - Real.logb 3 (4 ^ (Real.logb 3 x)) = 8 ↔ x = 81 := by
  constructor
  · -- Assume left side equals 8, prove x = 81
    intro h_eq
    have h1 : Real.logb 3 (x ^ (Real.logb 3 36)) = Real.logb 3 36 * Real.logb 3 x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        try norm_num
        try linarith
    have h2 : Real.logb 3 (4 ^ (Real.logb 3 x)) = Real.logb 3 x * Real.logb 3 4 := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        norm_num
    rw [h1, h2] at h_eq
    have h3 : Real.logb 3 36 = Real.logb 3 4 + 2 := by
      calc
        Real.logb 3 36 = Real.logb 3 (4 * (3 ^ 2 : ℝ)) := by norm_num
        _ = Real.logb 3 (4 : ℝ) + Real.logb 3 (3 ^ 2 : ℝ) := by
          rw [Real.logb_mul (by norm_num) (by norm_num)]
        _ = Real.logb 3 (4 : ℝ) + (2 : ℝ) * Real.logb 3 (3 : ℝ) := by
          simp [Real.logb_pow]
        _ = Real.logb 3 (4 : ℝ) + (2 : ℝ) * (1 : ℝ) := by
          rw [Real.logb_self_eq_one (by norm_num)]
        _ = Real.logb 3 (4 : ℝ) + (2 : ℝ) := by ring
        _ = Real.logb 3 4 + 2 := by norm_num
    have h4 : Real.logb 3 36 - Real.logb 3 4 = 2 := by
      linarith [h3]
    have h5 : Real.logb 3 x = 4 := by
      nlinarith [h4]
    have h6 : x = (81 : ℝ) := by
      have h21 : Real.logb 3 x = 4 := h5
      have h22 : x = (3 : ℝ) ^ (Real.logb 3 x : ℝ) := by
        field_simp at *
      rw [h21] at h22
      norm_num at h22 ⊢
      linarith
    linarith [h6]
  · -- Assume x = 81, prove the equation equals 8
    intro h_eq
    rw [h_eq]
    have h1 : Real.logb 3 ((81 : ℝ) ^ (Real.logb 3 36)) = Real.logb 3 36 * Real.logb 3 (81 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        try norm_num
        try linarith
    have h2 : Real.logb 3 (81 : ℝ) = 4 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h4 : Real.logb 3 (4 ^ (Real.logb 3 (81 : ℝ))) = Real.logb 3 (81 : ℝ) * Real.logb 3 (4 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        norm_num
    rw [h1, h4]
    rw [h2]
    have h3 : Real.logb 3 36 = Real.logb 3 4 + 2 := by
      calc
        Real.logb 3 36 = Real.logb 3 (4 * (3 ^ 2 : ℝ)) := by norm_num
        _ = Real.logb 3 (4 : ℝ) + Real.logb 3 (3 ^ 2 : ℝ) := by
          rw [Real.logb_mul (by norm_num) (by norm_num)]
        _ = Real.logb 3 (4 : ℝ) + (2 : ℝ) * Real.logb 3 (3 : ℝ) := by
          simp [Real.logb_pow]
        _ = Real.logb 3 (4 : ℝ) + (2 : ℝ) * (1 : ℝ) := by
          rw [Real.logb_self_eq_one (by norm_num)]
        _ = Real.logb 3 (4 : ℝ) + (2 : ℝ) := by ring
        _ = Real.logb 3 4 + 2 := by norm_num
    nlinarith [h3]