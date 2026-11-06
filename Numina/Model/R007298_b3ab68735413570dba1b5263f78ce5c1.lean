import Mathlib

theorem algebra_11271 : Real.sqrt 50 + Real.sqrt 18 = 8 * Real.sqrt 2 := by
  have h1 : Real.sqrt 50 = 5 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1, h2]
  ring