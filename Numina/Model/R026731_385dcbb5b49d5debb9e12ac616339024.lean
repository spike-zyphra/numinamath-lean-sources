import Mathlib

theorem algebra_10660 (x : ℝ) (hx : 3 * x > 0) : Real.logb 12 (3 * x) = 2 ↔ x = 48 := by
  constructor
  · -- Assume Real.logb 12 (3 * x) = 2, prove x = 48
    intro h
    have h1 : 3 * x = (12 : ℝ) ^ (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] at h
      · linarith
      all_goals linarith
    have h2 : (12 : ℝ) ^ (2 : ℝ) = (144 : ℝ) := by norm_num
    rw [h2] at h1
    have h3 : x = 48 := by
      linarith
    exact h3
  · -- Assume x = 48, prove Real.logb 12 (3 * x) = 2
    intro h
    rw [h]
    have h4 : Real.logb 12 (3 * (48 : ℝ)) = 2 := by
      have h5 : Real.logb 12 (3 * (48 : ℝ)) = Real.log (3 * (48 : ℝ)) / Real.log (12 : ℝ) := by
        field_simp [Real.logb]
      rw [h5]
      have h6 : Real.log (3 * (48 : ℝ)) = 2 * Real.log (12 : ℝ) := by
        calc 
          Real.log (3 * (48 : ℝ)) = Real.log (144 : ℝ) := by norm_num
          _ = Real.log ((12 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log (12 : ℝ) := by simp [Real.log_pow]
      rw [h6]
      field_simp
      <;> norm_num
    exact h4