import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_162268 (f : ℝ → ℝ) (hf : f = sin) :
    deriv f = cos := by
  rw [hf]
  apply Real.deriv_sin