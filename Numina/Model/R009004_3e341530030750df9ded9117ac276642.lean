import Mathlib

theorem algebra_11600 : Real.sqrt 5 - Real.sqrt 20 + Real.sqrt 45 = 2 * Real.sqrt 5 := by 
  have h1 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : Real.sqrt 45 = 3 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1, h2]
  ring