import Mathlib


theorem algebra_21033 :
    Real.sqrt 15 * Real.sqrt 35 = 5 * Real.sqrt 21 := by
  have h1 : Real.sqrt 15 * Real.sqrt 35 = Real.sqrt (15 * 35) := by
    rw [← Real.sqrt_mul (by norm_num)]
  have h2 : Real.sqrt (15 * 35) = Real.sqrt 525 := by
    norm_num
  have h3 : Real.sqrt 525 = 5 * Real.sqrt 21 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h1, h2, h3]