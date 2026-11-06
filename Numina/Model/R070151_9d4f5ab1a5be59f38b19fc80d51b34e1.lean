import Mathlib

theorem algebra_11602 : Complex.abs (5 / 6 + 2 * Complex.I) = 13 / 6 := by
  simp [Complex.abs, Complex.normSq]
  ring_nf
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num