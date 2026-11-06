import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

/- Two transformations are applied to the complex number $-3 - 8i$:

A $45^\circ$ rotation around the origin in the counter-clockwise direction.
A dilation, centered at the origin, with scale factor $\sqrt{2}.$

What is the resulting complex number? -/
theorem calculus_14745 (z : ℂ) (hz : z = -3 - 8 * I) :
    (Complex.exp (I * Real.pi / 4) * z) * (Real.sqrt 2) = 5 - 11 * I := by
  -- Substitute hz into the goal and do some simplifications according to complex number arithmetic.
  rw [hz, mul_div_assoc, mul_comm I (Real.pi / 4),  <-Complex.cos_add_sin_I, show (Real.pi / 4 : ℂ) = (Real.pi / 4 : ℝ) by norm_num, <-Complex.ofReal_cos, <-Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  field_simp
  rw [mul_comm, <-mul_assoc, mul_add, <-mul_assoc]
  norm_cast
  rw [Real.mul_self_sqrt]
  rify
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  norm_num
  
  