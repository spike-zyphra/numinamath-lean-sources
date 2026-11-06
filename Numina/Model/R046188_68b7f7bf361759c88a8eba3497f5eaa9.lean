import Mathlib

theorem algebra_10982 (x : ℝ) (hx : x > 0) : (4 : ℝ) ^ Real.logb 7 x = 16 ↔ x = 49 := by
  constructor
  · -- Assume (4 : ℝ) ^ Real.logb 7 x = 16, prove x = 49
    intro h
    have h1 : Real.logb 7 x = 2 := by
      have h2 : Real.logb 4 ((4 : ℝ) ^ Real.logb 7 x) = Real.logb 4 (16 : ℝ) := by
        rw [h]
      have h3 : Real.logb 4 ((4 : ℝ) ^ Real.logb 7 x) = Real.logb 7 x := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h4 : Real.logb 4 (16 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h3] at h2
      linarith [h4, h2]
    have h2 : x = (7 : ℝ) ^ (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] at h1
      · -- $\log_7 x = 2$ means $x = 7^2$
        linarith
      all_goals linarith
    rw [h2]
    norm_num
  · -- Assume x = 49, prove (4 : ℝ) ^ Real.logb 7 x = 16
    intro h
    rw [h]
    have h1 : Real.logb 7 (49 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h1]
    all_goals norm_num