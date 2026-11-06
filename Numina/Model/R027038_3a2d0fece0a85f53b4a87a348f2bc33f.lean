import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_298192 {p q : ℂ} (f : ℂ → ℂ)
  (h₀ : ∀ z, f z = (4 + I) * z ^ 2 + p * z + q)
  (h₁ : ∃ r : ℝ, f 1 = r) (h₂ : ∃ r : ℝ, f I = r) :
  abs p + abs q ≥ Real.sqrt 2 := by
  rcases h₁ with ⟨r₁, hr₁⟩
  rcases h₂ with ⟨r₂, hr₂⟩
  have eq₁ : f 1 = (4 + I) * (1 : ℂ) ^ 2 + p * (1 : ℂ) + q := h₀ 1
  rw [eq₁] at hr₁
  have eq₂ : f I = (4 + I) * (I : ℂ) ^ 2 + p * (I : ℂ) + q := h₀ I
  rw [eq₂] at hr₂
  have eq3 := congr_arg Complex.im hr₁
  simp [Complex.add_im, pow_two, Complex.mul_im] at eq3
  have eq4 := congr_arg Complex.im hr₂
  simp [pow_two, Complex.mul_im, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq4
  have eq5 : p.im + q.im = -1 := by
    linarith
  have eq6 : p.re + q.im = 1 := by
    linarith
  have h3 : abs p = Real.sqrt (p.re ^ 2 + p.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  have h4 : abs q = Real.sqrt (q.re ^ 2 + q.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [h3, h4]
  have h5 : p.re = 1 - q.im := by
    linarith
  have h6 : p.im = -1 - q.im := by
    linarith
  have h7 : Real.sqrt (p.re ^ 2 + p.im ^ 2) = Real.sqrt (2 * (1 + q.im ^ 2)) := by
    rw [show p.re = 1 - q.im by linarith, show p.im = -1 - q.im by linarith]
    have h8 : (1 - q.im : ℝ) ^ 2 + (-1 - q.im : ℝ) ^ 2 = 2 * (1 + q.im ^ 2) := by
      nlinarith
    rw [h8]
  have h8 : Real.sqrt (2 * (1 + q.im ^ 2)) ≥ Real.sqrt 2 := by
    have h9 : 2 * (1 + q.im ^ 2) ≥ 2 := by
      nlinarith [sq_nonneg (q.im : ℝ)]
    have h10 : Real.sqrt (2 * (1 + q.im ^ 2)) ≥ Real.sqrt (2 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    exact h10
  have h11 : Real.sqrt (q.re ^ 2 + q.im ^ 2) ≥ 0 := by
    positivity
  nlinarith [Real.sqrt_nonneg (2 * (1 + q.im ^ 2)), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (q.re ^ 2 + q.im ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (1 + q.im ^ 2) by nlinarith [sq_nonneg (q.im : ℝ)]), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ q.re ^ 2 + q.im ^ 2 by positivity)]