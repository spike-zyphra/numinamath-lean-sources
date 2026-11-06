import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_23116 (z : ℂ) (hz : z = 3 * Real.sqrt 3 - 5 * .I) :
    z * Complex.exp (Complex.I * Real.pi / 3) = 4 * Real.sqrt 3 + 2 * .I := by
  rw [hz]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im]
  ring_nf
  <;> simp [Real.sin_pi_div_three, Real.cos_pi_div_three, mul_add, mul_sub, pow_two, Real.sqrt_mul_self]
  <;> ring_nf
  <;> norm_num
  <;> ring
  all_goals linarith [Real.sqrt_nonneg 3]