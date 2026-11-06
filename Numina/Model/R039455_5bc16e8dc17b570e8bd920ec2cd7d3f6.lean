import Mathlib

theorem algebra_6690 (x : ℝ) (hx : 0 < x) (h : Real.logb 2 x + Real.logb 4 x = 6) :
    x = 16 := by

  have h1 : Real.logb 4 x = Real.logb 2 x / 2 := by
    have h2 : Real.logb 4 x = Real.logb 2 x / Real.logb 2 (4 : ℝ) := by
      field_simp [Real.logb]
      all_goals linarith

    have h3 : Real.logb 2 (4 : ℝ) = (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num

    rw [h3] at h2
    linarith

  rw [h1] at h

  have h2 : Real.logb 2 x = 4 := by
    linarith

  have h3 : x = 16 := by
    have h4 : x = (2 : ℝ) ^ (4 : ℝ) := by
      rw [← h2]
      field_simp [Real.rpow_logb]
      all_goals linarith
    norm_num at h4 ⊢
    linarith
  exact h3