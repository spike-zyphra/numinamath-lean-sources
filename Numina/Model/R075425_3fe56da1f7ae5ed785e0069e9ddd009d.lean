import Mathlib

theorem algebra_136726 : ((2^20 + 2^27 + 2^31 + 2^32 + 2^37 + 2^40) : ℝ) ^ ((1 : ℝ) / 4) = 1056 := by
  have h1 : ((2 : ℝ) ^ 20 + (2 : ℝ) ^ 27 + (2 : ℝ) ^ 31 + (2 : ℝ) ^ 32 + (2 : ℝ) ^ 37 + (2 : ℝ) ^ 40) = (1056 : ℝ) ^ 4 := by norm_num
  rw [h1]
  have h2 : ((1056 : ℝ) ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = (1056 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num
  exact h2