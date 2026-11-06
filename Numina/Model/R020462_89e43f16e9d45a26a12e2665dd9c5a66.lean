import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_123459 {f : ℝ → ℝ} (x₁ x₂ : ℝ) (h₁ : x₁ < x₂)
  (h₂ : ConvexOn ℝ (Set.Ioo x₁ x₂) f) :
  ContinuousOn f (Set.Ioo x₁ x₂) := by
  apply h₂.continuousOn
  apply isOpen_Ioo