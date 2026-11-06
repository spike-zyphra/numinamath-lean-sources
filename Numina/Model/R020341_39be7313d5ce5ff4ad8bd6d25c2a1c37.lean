import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_297232 {a b c x : ℂ}
  (ha : a = 1 + Complex.I) (hb : b = 2 + Complex.I) (hc : c = 3 + Complex.I)
  (hx : x = -1/2 + Real.sqrt 3/2 * Complex.I) :
  abs (a + b * x + c * x^2) = Real.sqrt 3 := by

  rw [ha, hb, hc, hx]

  have h1 : ((1 + Complex.I : ℂ) + (2 + Complex.I) * (-1 / 2 + Real.sqrt 3 / 2 * Complex.I) + (3 + Complex.I) * (-1 / 2 + Real.sqrt 3 / 2 * Complex.I) ^ 2) = (-3 / 2 : ℂ) - (Real.sqrt 3 / 2) * Complex.I := by
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    ring_nf
    <;> norm_num [Real.sqrt_sq]
    <;> ring

  rw [h1]

  simp [Complex.abs, Complex.normSq]
  ring_nf
  <;> norm_num [Real.sqrt_sq]
  all_goals linarith