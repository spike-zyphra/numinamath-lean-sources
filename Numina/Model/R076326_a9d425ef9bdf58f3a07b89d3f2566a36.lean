import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_77188 (f : ℝ → ℝ)
  (h₁ : ∀ x y, f x + f y ≥ x * y)
  (h₂ : ∀ x, ∃ y, f x + f y = x * y) :
  ∀ x, f x = x ^ 2 / 2 := by
    have h3 : ∀ x, f x ≥ x^2 / 2 := by
      intro x
      have h4 := h₁ x x
      have h5 : f x + f x ≥ x * x := by linarith
      have h6 : 2 * f x ≥ x ^ 2 := by linarith
      linarith
    intro x
    have h4 := h₂ x
    rcases h4 with ⟨y, hy⟩
    have h5 : f x ≥ x^2 / 2 := h3 x
    have h6 : f y ≥ y^2 / 2 := h3 y
    nlinarith [sq_nonneg (x - y)]