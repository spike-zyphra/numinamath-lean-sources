import Mathlib

theorem algebra_126657 (a b : ℝ) (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x)
    (h₁ : 1 ≤ f (-1) ∧ f (-1) ≤ 2) (h₂ : 2 ≤ f 1 ∧ f 1 ≤ 4) :
    3 ≤ f (-2) ∧ f (-2) ≤ 12 := by
  have h1₁ : 1 ≤ f (-1) := h₁.1
  have h1₂ : f (-1) ≤ 2 := h₁.2
  have h2₁ : 2 ≤ f 1 := h₂.1
  have h2₂ : f 1 ≤ 4 := h₂.2

  have h3 : f (-1) = a * (-1) ^ 2 + b * (-1) := by
    rw [hf]
  have h4 : f 1 = a * (1) ^ 2 + b * (1) := by
    rw [hf]
  have h5 : f (-2) = a * (-2) ^ 2 + b * (-2) := by
    rw [hf]

  rw [h3] at h1₁ h1₂
  rw [h4] at h2₁ h2₂
  rw [h5]

  constructor
  · -- We need to prove 3 ≤ f(-2)
    nlinarith
  · -- We need to prove f(-2) ≤ 12
    nlinarith