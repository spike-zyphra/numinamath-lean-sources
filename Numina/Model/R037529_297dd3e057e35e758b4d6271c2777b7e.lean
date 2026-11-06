import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_598841 (f : ℝ → ℝ) (hf : f = λ x => (1/3)*x^3 - x)
  (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Icc (-1) 1) (hx₂ : x₂ ∈ Icc (-1) 1) :
  |f x₁ - f x₂| ≤ 4/3 := by
    have hx₁1 : -1 ≤ x₁ := by
      have h1 : x₁ ∈ Icc (-1 : ℝ) 1 := hx₁
      exact h1.1
    have hx₁2 : x₁ ≤ 1 := by
      have h1 : x₁ ∈ Icc (-1 : ℝ) 1 := hx₁
      exact h1.2
    have hx₂1 : -1 ≤ x₂ := by
      have h2 : x₂ ∈ Icc (-1 : ℝ) 1 := hx₂
      exact h2.1
    have hx₂2 : x₂ ≤ 1 := by
      have h2 : x₂ ∈ Icc (-1 : ℝ) 1 := hx₂
      exact h2.2
    have hfx₁ : f x₁ = (1 / 3) * x₁ ^ 3 - x₁ := by
      rw [hf]
    have hfx₂ : f x₂ = (1 / 3) * x₂ ^ 3 - x₂ := by
      rw [hf]
    have h1 : -2 / 3 ≤ f x₁ := by
      rw [hfx₁]
      nlinarith [sq_nonneg (x₁ + 1), sq_nonneg (x₁ - 1), sq_nonneg (x₁), sq_nonneg (x₁ - (-1)), sq_nonneg (x₁ - 1)]
    have h2 : f x₁ ≤ 2 / 3 := by
      rw [hfx₁]
      nlinarith [sq_nonneg (x₁ + 1), sq_nonneg (x₁ - 1), sq_nonneg (x₁), sq_nonneg (x₁ - (-1)), sq_nonneg (x₁ - 1)]
    have h3 : -2 / 3 ≤ f x₂ := by
      rw [hfx₂]
      nlinarith [sq_nonneg (x₂ + 1), sq_nonneg (x₂ - 1), sq_nonneg (x₂), sq_nonneg (x₂ - (-1)), sq_nonneg (x₂ - 1)]
    have h4 : f x₂ ≤ 2 / 3 := by
      rw [hfx₂]
      nlinarith [sq_nonneg (x₂ + 1), sq_nonneg (x₂ - 1), sq_nonneg (x₂), sq_nonneg (x₂ - (-1)), sq_nonneg (x₂ - 1)]
    have h5 : -4 / 3 ≤ f x₁ - f x₂ := by
      linarith
    have h6 : f x₁ - f x₂ ≤ 4 / 3 := by
      linarith
    apply abs_le.mpr
    constructor
    · linarith
    · linarith