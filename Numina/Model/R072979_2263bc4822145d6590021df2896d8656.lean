import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_140399
  (f : ℝ → ℝ)
  (x₀ : ℝ)
  (h₀ : f = λ x => 2 * x ^ 2 + 8)
  (h₁ : x₀ = 5) :
  ContinuousAt f x₀ := by
  rw [h₀, h₁]
  apply ContinuousAt.add
  · apply ContinuousAt.mul
    · exact continuousAt_const
    · apply ContinuousAt.pow
      exact continuousAt_id
  · exact continuousAt_const