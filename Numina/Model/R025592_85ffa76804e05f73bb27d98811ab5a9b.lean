import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_23187 (z : ℂ) (hz : z = Real.sqrt 2 - 5 * Real.sqrt 2 * .I)
  (θ : ℝ) (hθ : θ = 135 * Real.pi / 180) :
  z * (Complex.exp (I * θ)) = 4 + 6 * .I := by
  rw [hz, hθ]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have h1 : 135 * Real.pi / 180 = 3 * Real.pi / 4 := by
    ring_nf
  have h2 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
    have h1 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by
      ring_nf
    rw [h1]
    rw [Real.cos_pi_sub]
    have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    linarith
  have h3 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    have h1 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by
      ring_nf
    rw [h1]
    rw [Real.sin_pi_sub]
    have h4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    linarith
  have eq3 : Real.cos (135 * Real.pi / 180) = -Real.sqrt 2 / 2 := by
    rw [show 135 * Real.pi / 180 = 3 * Real.pi / 4 by ring_nf]
    linarith [h2]
  have eq4 : Real.sin (135 * Real.pi / 180) = Real.sqrt 2 / 2 := by
    rw [show 135 * Real.pi / 180 = 3 * Real.pi / 4 by ring_nf]
    linarith [h3]
  constructor
  · -- Real part matches.
    ring_nf at *
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Imaginary part matches.
    ring_nf at *
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]