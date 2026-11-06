import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_143971
  (f : ℝ → ℝ)
  (x₀ : ℝ)
  (h₀ : f = λ x => -3 * x ^ 2 - 6)
  (h₁ : x₀ = 1) :
  ContinuousAt f x₀ := by 
  rw [h₀, h₁]
  apply ContinuousAt.sub
  · apply ContinuousAt.mul
    · exact continuousAt_const
    · apply ContinuousAt.pow
      exact continuousAt_id
  · exact continuousAt_const