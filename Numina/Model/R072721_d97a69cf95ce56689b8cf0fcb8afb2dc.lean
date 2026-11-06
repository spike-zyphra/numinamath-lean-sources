import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_219987 {z : ℂ} (hz : z ≠ 0) :
    {w | ∃ k : ℤ, w = log (abs z) + I * (arg z + 2 * k * π)} = {log (abs z) + I * (arg z + 2 * k * π) | k : ℤ} := by 
  ext w 
  simp
  <;> tauto