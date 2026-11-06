import Mathlib

theorem algebra_14532 : Real.sqrt 180 = 6 * Real.sqrt 5 := by
  have h1 : Real.sqrt 180 = Real.sqrt (36 * (5 : ℝ)) := by
    norm_num
  rw [h1]
  have h2 : Real.sqrt (36 * (5 : ℝ)) = Real.sqrt (36 : ℝ) * Real.sqrt (5 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
  rw [h2]
  have h3 : Real.sqrt (36 : ℝ) = (6 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h3]
  all_goals ring_nf <;> norm_num [Real.sqrt_nonneg]