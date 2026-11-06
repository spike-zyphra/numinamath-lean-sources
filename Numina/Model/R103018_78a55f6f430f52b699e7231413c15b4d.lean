import Mathlib

theorem algebra_10707 : Real.sqrt (Real.sqrt (1 / 4096) ^ ((1 : ℝ) / 3)) = 1 / 2 := by
  have h1 : Real.sqrt (1 / 4096 : ℝ) = 1 / 64 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : (Real.sqrt (1 / 4096 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = 1 / 4 := by
    rw [h1]
    have h3 : ((1 / 64 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (1 / 4 : ℝ) := by
      have h4 : ((1 / 64 : ℝ) : ℝ) = (1 / 4) ^ (3 : ℝ) := by norm_num
      rw [h4]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
      all_goals linarith
    linarith [h3]
  rw [h2]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> norm_num
  <;> ring_nf
  <;> norm_num