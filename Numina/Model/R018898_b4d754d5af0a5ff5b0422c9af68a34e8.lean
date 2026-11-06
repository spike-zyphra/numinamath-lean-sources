import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_22600 : exp (π * I) = -1 := by 
  have h1 : exp (π * I) = exp (0 + π * I) := by 
    simp 
  rw [h1]
  simp [Complex.exp_add_mul_I, Real.sin_pi, Real.cos_pi]
  all_goals norm_num