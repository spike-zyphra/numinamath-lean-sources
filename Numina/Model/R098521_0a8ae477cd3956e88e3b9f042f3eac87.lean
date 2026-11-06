import Mathlib

theorem algebra_199630 {P : ℝ} (hP : P = ((6 ^ ((1 : ℝ) / 3)) * (1 / 162) ^ ((1 : ℝ) / 3)) ^ (-1 : ℝ)) : P = 3 := by
  rw [hP]
  have h1 : (6 : ℝ) ^ ((1 : ℝ) / 3) * (1 / 162 : ℝ) ^ ((1 : ℝ) / 3) = (1 / 27 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h2 : (6 : ℝ) * (1 / 162 : ℝ) = (1 / 27 : ℝ) := by
      norm_num
    have h3 : (6 : ℝ) ^ ((1 : ℝ) / 3) * (1 / 162 : ℝ) ^ ((1 : ℝ) / 3) = ((6 : ℝ) * (1 / 162 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals
        positivity
    rw [h3]
    rw [h2]
  have h4 : (1 / 27 : ℝ) ^ ((1 : ℝ) / 3) = (1 / 3 : ℝ) := by
    have h5 : (1 / 27 : ℝ) = (3 : ℝ) ^ (-3 : ℝ) := by
      norm_num
    rw [h5]
    rw [← Real.rpow_mul]
    norm_num
    all_goals
      norm_num
  rw [h1, h4]
  norm_num