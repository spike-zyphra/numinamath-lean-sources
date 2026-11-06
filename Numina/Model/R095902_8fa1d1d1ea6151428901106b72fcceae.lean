import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_146201 : Differentiable ℂ (exp) := by 
  apply Complex.differentiable_exp