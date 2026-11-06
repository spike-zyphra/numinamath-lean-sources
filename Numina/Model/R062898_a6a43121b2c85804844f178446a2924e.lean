import Mathlib

theorem algebra_19248 : Real.sqrt (Real.sqrt (1 / 729) ^ ((1 : ℝ) / 3)) = Real.sqrt 3 / 3 := by

  have h1 : Real.sqrt (1 / 729 : ℝ) = 1 / 27 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  have h2 : (Real.sqrt (1 / 729 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (1 / 3) := by
    rw [h1]
    have h3 : ((1 / 27 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (1 / 3 : ℝ) := by
      have h4 : ((1 / 27 : ℝ) : ℝ) = ((3 : ℝ) ^ (-3 : ℝ)) := by
        norm_num
      rw [h4]
      have h5 : ((3 : ℝ) ^ (-3 : ℝ)) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h5]
      norm_num
    rw [h3]

  have h3 : Real.sqrt ((1 / 3 : ℝ)) = Real.sqrt 3 / 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  rw [h2]
  rw [h3]
  all_goals norm_num