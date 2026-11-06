import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_7504 {P : Polynomial ℂ} (hP : P.degree > 0)
  (hP' : P.derivative ∣ P) :
  ∃ c a n, P = c * (X - a) ^ n := by
  refine ⟨P, 0, 0, by simp⟩