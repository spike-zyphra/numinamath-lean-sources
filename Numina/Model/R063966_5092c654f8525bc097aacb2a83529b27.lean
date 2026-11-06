import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_23465 {z c : ℂ} (hz : z = 2 + Real.sqrt 2 - (3 + 3 * Real.sqrt 2) * .I)
  (hc : c = 2 - 3 * .I) (w : ℂ) (hw : w = (z - c) * (Complex.exp (Complex.I * Real.pi / 4)) + c) :
  w = 6 - 5 * .I := by 
  rw [hw, hz, hc]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        Complex.exp_re, Complex.exp_im, Complex.I_re, Complex.I_im, mul_add, mul_comm]
  ring_nf
  <;> simp [Real.sqrt_sq, Real.sin_pi_div_four, Real.cos_pi_div_four]
  <;> ring_nf
  <;> norm_num
  <;> ring