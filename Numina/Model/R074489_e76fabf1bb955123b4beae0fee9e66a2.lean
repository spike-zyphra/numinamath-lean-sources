import Mathlib

theorem algebra_187805 (x : ℝ) (hx : x > 0) :
    Real.logb 2 x + Real.logb 4 x + Real.logb 8 x = 11 ↔ x = 64 := by
  constructor
  · -- Forward direction: assuming Real.logb 2 x + Real.logb 4 x + Real.logb 8 x = 11, proving x = 64
    intro h
    have h1 : Real.logb 4 x = Real.logb 2 x / 2 := by
      have h4 : Real.logb 4 x = Real.logb 2 x / Real.logb 2 (4 : ℝ) := by
        field_simp [Real.logb]
        all_goals linarith [Real.log_pos (by norm_num : (4 : ℝ) > 1)]
      have h2 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h2] at h4
      linarith
    have h2 : Real.logb 8 x = Real.logb 2 x / 3 := by
      have h8 : Real.logb 8 x = Real.logb 2 x / Real.logb 2 (8 : ℝ) := by
        field_simp [Real.logb]
        all_goals linarith [Real.log_pos (by norm_num : (8 : ℝ) > 1)]
      have h3 : Real.logb 2 (8 : ℝ) = 3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h3] at h8
      linarith
    rw [h1, h2] at h
    have h3 : Real.logb 2 x = 6 := by
      have eq1 : Real.logb 2 x + (Real.logb 2 x / 2) + (Real.logb 2 x / 3) = 11 := h
      linarith
    have h4 : x = (2 : ℝ) ^ (6 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] at h3
      · -- Real.logb_eq_iff_rpow_eq expands Real.logb 2 x = 6 into x = 2^6
        linarith [h3]
      all_goals linarith [show x > 0 by linarith, show (2 : ℝ) > 1 by norm_num]
    rw [h4]
    norm_num
  · -- Backward direction: assuming x = 64, proving Real.logb 2 x + Real.logb 4 x + Real.logb 8 x = 11
    intro h
    rw [h]
    have h1 : Real.logb 2 (64 : ℝ) = 6 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h2 : Real.logb 4 (64 : ℝ) = 3 := by
      have h4 : Real.logb 4 (64 : ℝ) = Real.logb 2 (64 : ℝ) / Real.logb 2 (4 : ℝ) := by
        field_simp [Real.logb]
        all_goals
          linarith [Real.log_pos (by norm_num : (4 : ℝ) > 1)]
      have h31 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h4, h1, h31]
      all_goals norm_num
    have h3 : Real.logb 8 (64 : ℝ) = 2 := by
      have h8 : Real.logb 8 (64 : ℝ) = Real.logb 2 (64 : ℝ) / Real.logb 2 (8 : ℝ) := by
        field_simp [Real.logb]
        all_goals
          linarith [Real.log_pos (by norm_num : (8 : ℝ) > 1)]
      have h32 : Real.logb 2 (8 : ℝ) = 3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h8, h1, h32]
      all_goals norm_num
    rw [h1, h2, h3]
    all_goals norm_num