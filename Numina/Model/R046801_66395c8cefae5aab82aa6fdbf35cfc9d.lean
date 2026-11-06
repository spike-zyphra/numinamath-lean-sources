import Mathlib

open Real Set
open scoped BigOperators

  theorem calculus_156743 (f : ℝ → ℝ) (hf : f = λ x => x ^ 2) :
  ∫ x in (1)..2, f x = 7 / 3 := by
  rw [hf]
  norm_num [Finset.sum_range_succ, mul_comm]