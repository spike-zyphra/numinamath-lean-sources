import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_250386 (z : ℂ) (hz : z = 3 - Real.sqrt 3 * .I) :
    (z * .exp (-Real.pi / 3 * .I)) = -2 * Real.sqrt 3 * .I := by
  rw [hz]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        Complex.exp_re, Complex.exp_im]
  have h1 : Real.cos (-Real.pi / 3) = 1 / 2 := by
    have h2 : Real.cos (-Real.pi / 3) = Real.cos (Real.pi / 3) := by
      rw [show -Real.pi / 3 = - (Real.pi / 3) by ring]
      rw [Real.cos_neg]
    rw [h2]
    exact Real.cos_pi_div_three
  have h2 : Real.sin (-Real.pi / 3) = -Real.sqrt 3 / 2 := by
    have h3 : Real.sin (-Real.pi / 3) = - Real.sin (Real.pi / 3) := by
      rw [show -Real.pi / 3 = - (Real.pi / 3) by ring]
      rw [Real.sin_neg]
    rw [h3]
    rw [Real.sin_pi_div_three]
    all_goals ring
  simp [h1, h2]
  <;> ring_nf <;> norm_num [pow_two, mul_add, mul_sub]
  all_goals ring