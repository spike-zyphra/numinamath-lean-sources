import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_152217 (u : ℝ → ℝ) (hu : u = λ r => sin r)
  (r : ℝ) (hr : r > 0) :
  deriv (λ x => u (x)) r = cos r := by 
  rw [hu]
  simp