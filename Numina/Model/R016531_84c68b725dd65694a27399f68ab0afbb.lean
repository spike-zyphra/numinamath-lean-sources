import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_1476
  (f : ℝ → ℝ)
  (h₀ : Function.Bijective f)
  (h₁ : ∀ x, f x ∈ Set.Ico 0 1) :
  Set.Infinite {x | ¬ ContinuousAt f x} ∧
  ¬ Countable {x | ¬ ContinuousAt f x} := by
  have h2 := h₀.surjective
  specialize h2 1
  rcases h2 with ⟨x, hx⟩
  have h3 := h₁ x
  simp at h3
  linarith