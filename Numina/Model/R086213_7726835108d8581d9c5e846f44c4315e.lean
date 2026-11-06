import Mathlib

theorem algebra_297147 : ((-2 : ℝ)^4)^(-3 / 4 : ℝ) = 1 / 8 := by
  have h1 : (-2 : ℝ) ^ 4 = (16 : ℝ) := by norm_num
  rw [h1]
  have h5 : (16 : ℝ) ^ (-3 / 4 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) := by
    have h6 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h6]
    have h7 : ((2 : ℝ) ^ (4 : ℝ)) ^ (-3 / 4 : ℝ) = (2 : ℝ) ^ (4 * (-3 / 4) : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf at *
      all_goals norm_num
      all_goals nlinarith
      all_goals norm_num
    rw [h7]
    all_goals norm_num
  rw [h5]
  norm_num
  all_goals norm_num
  all_goals nlinarith
  all_goals norm_num