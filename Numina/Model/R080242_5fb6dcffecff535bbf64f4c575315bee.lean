import Mathlib

theorem algebra_4040 : (1600 : ℝ) ^ ((1 : ℝ) / 4) = 2 * Real.sqrt 10 := by
  have h1 : (1600 : ℝ) ^ ((1 : ℝ) / 4) = ((16 : ℝ) * (10 : ℝ) ^ 2) ^ ((1 : ℝ) / 4) := by
    norm_num
  rw [h1]
  have h2 : ((16 : ℝ) * (10 : ℝ) ^ 2) ^ ((1 : ℝ) / 4) = (16 : ℝ) ^ ((1 : ℝ) / 4) * ((10 : ℝ) ^ 2) ^ ((1 : ℝ) / 4) := by
    rw [← Real.mul_rpow]
    all_goals norm_num
  rw [h2]
  have h3 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
    have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h16]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h4 : ((10 : ℝ) ^ 2) ^ ((1 : ℝ) / 4) = Real.sqrt 10 := by
    have h5 : ((10 : ℝ) ^ 2) ^ ((1 : ℝ) / 4) = (10 : ℝ) ^ (2 * (1 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h5]
    have h6 : (10 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 10 := by
      have h10 : (10 : ℝ) ^ (2 * (1 / 4 : ℝ)) = (10 : ℝ) ^ (1 / 2 : ℝ) := by
        norm_num
        <;> ring_nf <;> norm_num
      rw [h10]
      have h7 : (10 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 10 := by
        rw [Real.sqrt_eq_rpow]
      rw [h7]
    rw [h6]
  rw [h3, h4]
  all_goals norm_num