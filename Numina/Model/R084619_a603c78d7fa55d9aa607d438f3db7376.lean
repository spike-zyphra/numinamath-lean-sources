import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_228938 {f : ℝ → ℝ} (x₀ : ℝ) (h : DifferentiableAt ℝ f x₀) :
  ContinuousAt f x₀ := by
  exact h.continuousAt