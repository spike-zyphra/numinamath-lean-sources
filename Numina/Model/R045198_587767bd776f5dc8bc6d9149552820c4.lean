import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_38239 (α : ℝ) :
  Continuous (λ x => (α + abs x)^2 * Real.exp ((5 - abs x)^2)) ↔
  True := by 
  constructor
  · -- Assume the function is continuous
    intro h
    trivial

  · -- Assume True
    intro h
    -- Show the function is continuous
    continuity