import Mathlib

theorem algebra_9343 {z : ℂ} (hz : z = - .I + 1) : ((z^2 - 2 * z) / (z - 1)) = - 2 * .I := by
  rw [hz]
  field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
  <;> norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]
  <;> ring_nf
  <;> norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]
  <;> ring
  <;> norm_num
  <;> ring_nf
  <;> norm_num