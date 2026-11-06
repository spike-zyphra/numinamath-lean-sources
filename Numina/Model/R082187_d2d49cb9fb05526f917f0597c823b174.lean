import Mathlib

open Real Set
open scoped Real

theorem algebra_163065 (α : ℝ) (h₀ : α ∈ Ioo 90 180) (h₁ : α ∈ Ioo 270 360) :
    sqrt ((1 + sin α) / (1 - sin α)) - sqrt ((1 - sin α) / (1 + sin α)) = -2 * tan α := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  linarith -- Contradiction because α cannot be in both intervals (90, 180) and (270, 360)