import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_18653 : abs (1 - 4 * I) = Real.sqrt 17 := by 
  simp [Complex.abs, Complex.normSq]
  norm_num