import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_598841 (f : ℝ → ℝ) (hf : f = λ x => (1/3)*x^3 - x)
  (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Icc (-1) 1) (hx₂ : x₂ ∈ Icc (-1) 1) :
  |f x₁ - f x₂| ≤ 4/3 := by
  rw [hf]
  simp at hx₁ hx₂
  have h1 : (1/3 : ℝ) * x₁ ^ 3 - x₁ - ((1/3 : ℝ) * x₂ ^ 3 - x₂) ≤ 4 / 3 := by
    nlinarith [sq_nonneg (x₁ + 1), sq_nonneg (x₁ - 1), sq_nonneg (x₂ + 1), sq_nonneg (x₂ - 1),
      sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂)]
  have h2 : -((1/3 : ℝ) * x₁ ^ 3 - x₁ - ((1/3 : ℝ) * x₂ ^ 3 - x₂)) ≤ 4 / 3 := by
    nlinarith [sq_nonneg (x₁ + 1), sq_nonneg (x₁ - 1), sq_nonneg (x₂ + 1), sq_nonneg (x₂ - 1),
      sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂)]
  apply abs_le.mpr
  constructor <;> linarith