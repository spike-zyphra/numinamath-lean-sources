import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_265648 (a : ℝ) (z1 z2 : ℂ)
  (h₁ : (1 + Complex.I) * z1 = -1 + 5 * Complex.I)
  (h₂ : z2 = a - 2 - Complex.I)
  (h₃ : abs (z1 - (z2.1 - Complex.I * z2.2)) < abs z1) :
  1 < a ∧ a < 7 := by
  have h4 : z1 = 2 + 3 * Complex.I := by
    have eq1 := h₁
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 ⊢
    norm_num at eq1 ⊢
    constructor <;> nlinarith
  have h5 : z2 = a - 2 - Complex.I := h₂
  have h8 : abs (z1 - (z2.1 - Complex.I * z2.2)) = Real.sqrt ((4 - a) ^ 2 + 4) := by
    rw [h4, h5]
    simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
    ring_nf
  have h9 : abs z1 = Real.sqrt 13 := by
    rw [h4]
    simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
    ring_nf
  rw [h8, h9] at h₃
  have h10 : (4 - a) ^ 2 + 4 < 13 := by
    have h11 : Real.sqrt ((4 - a) ^ 2 + 4) < Real.sqrt 13 := h₃
    have h12 : (Real.sqrt ((4 - a) ^ 2 + 4)) ^ 2 < (Real.sqrt 13) ^ 2 := by nlinarith [h11, Real.sqrt_nonneg ((4 - a) ^ 2 + 4), Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (4 - a) ^ 2 + 4 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    rw [Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by norm_num)] at h12
    linarith [h12]
  constructor
  · -- Prove 1 < a
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 7), h10]
  · -- Prove a < 7
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 7), h10]