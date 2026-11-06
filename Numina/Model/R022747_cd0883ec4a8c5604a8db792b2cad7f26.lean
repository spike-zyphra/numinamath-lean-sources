import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_165228 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = x * y) :
  Continuous f := by
  have h1 : f = fun x => fun y => x * y := by 
    funext x y
    exact h₀ x y 
  rw [h1]
  continuity