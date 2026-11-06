import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_128451 (Z : ℂ) (h : (Z - 1)^2 = abs (Z - 1)^2) :
    ∃ r : ℝ, Z = r := by
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.abs, Complex.normSq] at eq1 eq2 
  have h1 : Z.im = 0 := by 
    have eq3 : ( (Z.re - 1) ^ 2 - Z.im ^ 2 : ℝ ) = ( (Z.re - 1) ^ 2 + Z.im ^ 2 : ℝ ) := by
      ring_nf at eq1 ⊢
      nlinarith [ Real.sqrt_nonneg ( (Z.re - 1) ^ 2 + Z.im ^ 2 ), Real.sq_sqrt (show (0 : ℝ) ≤ (Z.re - 1) ^ 2 + Z.im ^ 2 by positivity ) ]
    have eq4 : Z.im ^ 2 = 0 := by 
      nlinarith 
    have : Z.im = 0 := by
      nlinarith 
    exact this 
  use Z.re
  simp [Complex.ext_iff, h1]
  all_goals linarith