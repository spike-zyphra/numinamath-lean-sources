import Mathlib

theorem algebra_20434 : Real.sqrt (40 * 9) / Real.sqrt 49 = 6 * Real.sqrt 10 / 7 := by
  have h1 : Real.sqrt (40 * 9) = Real.sqrt 360 := by
    norm_num
  have h2 : Real.sqrt 360 = 6 * Real.sqrt 10 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : Real.sqrt 49 = 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1, h2, h3]
  <;> ring_nf <;> norm_num