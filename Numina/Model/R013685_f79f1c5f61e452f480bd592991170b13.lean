import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem number_theory_313701 :
    (2 + I)^2 / (1 - I) ∈ {z : ℂ | z.re < 0 ∧ z.im > 0} := by
  have h1 : (2 + I)^2 / (1 - I) = (-1 / 2 + 7 / 2 * I) := by 
    field_simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
    norm_num
  rw [h1]
  constructor
  · -- Show that real part is negative
    norm_num
  · -- Show that imaginary part is positive
    norm_num