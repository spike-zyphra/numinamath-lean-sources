import Mathlib

theorem algebra_20561 {z : ℂ} (hz : z = 5 - 12 * .I) : Complex.abs z = 13 := by 
  rw [hz]
  simp [Complex.abs, Complex.normSq]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num