import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_229245 {f : ℝ → ℝ} (a b : ℝ) (x₀ : ℝ)
  (h₀ : a < b) (h₁ : x₀ ∈ Set.Ioo a b) (h₂ : DifferentiableAt ℝ f x₀)
  (h₃ : IsLocalMax f x₀ ∨ IsLocalMin f x₀) :
  deriv f x₀ = 0 := by
  rcases h₃ with (h | h)
  · -- Case where f(x₀) is a local maximum
    have h4 : deriv f x₀ = 0 := h.deriv_eq_zero
    exact h4
  · -- Case where f(x₀) is a local minimum
    have h5 : deriv f x₀ = 0 := h.deriv_eq_zero
    exact h5