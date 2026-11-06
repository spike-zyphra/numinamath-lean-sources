import Mathlib

theorem algebra_3628 : ∑ (i ∈ Finset.range 64), (i+1) * (.I : ℂ)^(i+1) = 32 - 32 * .I := by
  norm_num [Finset.sum_range_succ, pow_succ, Complex.ext_iff, Complex.I_mul_I]
  <;> ring_nf <;> norm_num [Complex.I_mul_I]
  <;> ring
  <;> norm_num [Complex.I_mul_I]