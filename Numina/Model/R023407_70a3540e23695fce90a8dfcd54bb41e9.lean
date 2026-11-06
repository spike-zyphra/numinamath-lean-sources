import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_165322 {Z : ℂ} (h : (Z - 1)^2 = abs (Z - 1)^2) :
    ∃ r : ℝ, Z = r := by
  have eq1 := congr_arg Complex.re h 
  have eq2 := congr_arg Complex.im h
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.abs, Complex.normSq] at eq1 eq2 
  have h1 : Z.im ^ 2 = 0 := by 
    nlinarith 
  have h2 : Z.im = 0 := by 
    simp at h1 ⊢ 
    <;> nlinarith 
  use Z.re 
  simp [Complex.ext_iff, h2]