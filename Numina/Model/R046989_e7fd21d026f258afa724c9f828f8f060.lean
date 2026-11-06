import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_14745 (z : ℂ) (hz : z = -3 - 8 * I) :
    (Complex.exp (I * Real.pi / 4) * z) * (Real.sqrt 2) = 5 - 11 * I := by
  rw [hz]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        Complex.exp_re, Complex.exp_im, mul_add, mul_comm, mul_assoc]
  ring_nf
  <;> simp [Real.sin_pi_div_four, Real.cos_pi_div_four, mul_add, mul_comm, Real.sq_sqrt]
  <;> ring_nf
  <;> norm_num [Real.sin_pi_div_four, Real.cos_pi_div_four, Real.sq_sqrt]
  <;> ring