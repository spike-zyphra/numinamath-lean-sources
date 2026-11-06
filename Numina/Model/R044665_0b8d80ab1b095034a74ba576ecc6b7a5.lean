import Mathlib

theorem algebra_21056 : √192 = 8 * √3 := by
  have h4 : Real.sqrt 192 = Real.sqrt (8 ^ 2 * (3 : ℝ)) := by
    norm_num
  rw [h4]
  have h5 : Real.sqrt ((8: ℝ) ^ 2 * (3: ℝ)) = Real.sqrt ((8: ℝ) ^ 2) * Real.sqrt (3: ℝ) := by
    rw [Real.sqrt_mul]
    all_goals norm_num
  rw [h5]
  have h6 : Real.sqrt ((8: ℝ) ^ 2) = (8: ℝ) := by
    rw [Real.sqrt_sq]
    all_goals norm_num
  rw [h6]
  <;> ring_nf <;> norm_num