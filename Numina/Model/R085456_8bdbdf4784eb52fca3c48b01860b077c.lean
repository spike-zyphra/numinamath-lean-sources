import Mathlib

theorem algebra_12049 (x : ℝ) (hx : 0 < x) : Real.logb 4 x + Real.logb 2 (x ^ 2) = 10 ↔ x = 16 := by
  constructor
  · -- Forward direction: if log_4 x + log_2 x^2 = 10, then x = 16
    intro h
    have h1 : Real.logb 4 x = Real.logb 2 x / 2 := by
      have h2 : Real.logb 4 x = Real.logb 2 x / Real.logb 2 (4 : ℝ) := by
        field_simp [Real.logb]
        all_goals linarith
      have h3 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h3] at h2
      linarith
    have h4 : Real.logb 2 (x ^ 2) = 2 * Real.logb 2 x := by
      simp [Real.logb_pow]
    rw [h1, h4] at h
    have h5 : Real.logb 2 x = 4 := by
      linarith
    have h6 : x = (2 : ℝ) ^ (4 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] at h5
      all_goals linarith
    norm_num at h6 ⊢
    exact h6
  · -- Reverse direction: if x = 16, then log_4 x + log_2 x^2 = 10
    intro h
    rw [h]
    have h1 : Real.logb 4 (16 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h2 : Real.logb 2 ((16 : ℝ) ^ 2) = 8 := by
      have h3 : Real.logb 2 ((16 : ℝ) ^ 2) = 2 * Real.logb 2 (16 : ℝ) := by
        simp [Real.logb_pow]
      have h4 : Real.logb 2 (16 : ℝ) = 4 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h3, h4]
      norm_num
    linarith [h1, h2]