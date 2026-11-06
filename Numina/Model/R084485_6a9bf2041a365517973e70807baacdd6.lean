import Mathlib

theorem algebra_274885 {x y : ℝ} (h₁ : (2 : ℝ)^x = 15) (h₂ : (15 : ℝ)^y = 32) : x * y = 5 := by
  have hx : x = Real.logb 2 15 := by
    rw [←h₁]
    field_simp
  have hy : y = Real.logb 15 32 := by
    rw [←h₂]
    field_simp
  rw [hx, hy]
  have h3 : Real.logb 2 15 * Real.logb 15 32 = Real.logb 2 32 := by
    have h4 : Real.logb 15 32 = Real.logb 2 32 / Real.logb 2 15 := by
      field_simp [Real.logb]
      all_goals linarith
    have h5 : Real.logb 2 15 ≠ 0 := by
      have h6 : (2 : ℝ) ^ Real.logb 2 15 = 15 := by
        field_simp
      by_contra h
      have h7 : Real.logb 2 15 = 0 := by linarith
      have h8 : (2 : ℝ) ^ (0 : ℝ) = 1 := by
        simp
      have h9 : (2 : ℝ) ^ Real.logb 2 15 = (2 : ℝ) ^ (0 : ℝ) := by
        rw [h7]
      rw [h6] at h9
      rw [h8] at h9
      all_goals linarith
    rw [h4]
    field_simp [h5]
    all_goals linarith
  have h10 : Real.logb 2 32 = 5 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  linarith [h3, h10]