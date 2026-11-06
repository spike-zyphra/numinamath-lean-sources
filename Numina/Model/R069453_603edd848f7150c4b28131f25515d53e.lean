import Mathlib

theorem algebra_10562 : Real.sqrt 8 * Real.sqrt 50 = 20 := by 
  have h1 : Real.sqrt 8 * Real.sqrt 50 = Real.sqrt (8 * 50) := by
    rw [← Real.sqrt_mul (by norm_num)]
  rw [h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num