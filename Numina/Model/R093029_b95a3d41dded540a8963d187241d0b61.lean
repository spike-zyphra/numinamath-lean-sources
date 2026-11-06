import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_122768
  (f : ℝ → ℝ) (x₀ : ℝ)
  (h₀ : f = λ x => 5 * x ^ 2 + 1) (h₁ : x₀ = 7) :
  ContinuousAt f x₀ := by 
  rw [h₀, h₁]
  apply ContinuousAt.add
  · -- Show that 5 * (x ^ 2) is continuous
    apply ContinuousAt.mul
    · -- Show that 5 is continuous
      exact continuousAt_const
    · -- Show that x ^ 2 is continuous
      apply ContinuousAt.pow
      exact continuousAt_id
  · -- Show that 1 is continuous
    exact continuousAt_const