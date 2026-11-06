import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_229843 (f : ℝ → ℝ) (hf : f = sin) :
    ∫ x in (0)..π, f x = 2 := by 
  rw [hf]
  norm_num [Real.sin_pi]