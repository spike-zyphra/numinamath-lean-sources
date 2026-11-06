import Mathlib

theorem algebra_19803 : Real.sqrt (Real.sqrt 4096 + (4096) ^ ((1 : ℝ) / 3) + (4096) ^ ((1 : ℝ) / 4)) = 2 * Real.sqrt 22 := by

  have h1 : Real.sqrt 4096 = 64 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num

  have h2 : (4096 : ℝ) ^ ((1 : ℝ) / 3) = 16 := by
    have h3 : (4096 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ (12 : ℝ)) ^ ((1 : ℝ) / 3) := by norm_num
    rw [h3]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num

  have h4 : (4096 : ℝ) ^ ((1 : ℝ) / 4) = 8 := by
    have h5 : (4096 : ℝ) ^ ((1 : ℝ) / 4) = ((2 : ℝ) ^ (12 : ℝ)) ^ ((1 : ℝ) / 4) := by norm_num
    rw [h5]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num

  rw [h1, h2, h4]

  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  <;> ring_nf <;> norm_num [Real.sq_sqrt]
  all_goals norm_num
  all_goals linarith [Real.sqrt_nonneg 22]