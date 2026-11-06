import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_152722 :
  ∃ x : ℝ, x = sqrt ((1 / 3) + (2 / 2) - (1 / 1)) * Real.tan (1 / 1) := by 
  refine ⟨sqrt ((1 / 3) + (2 / 2) - (1 / 1)) * Real.tan (1 / 1), rfl⟩