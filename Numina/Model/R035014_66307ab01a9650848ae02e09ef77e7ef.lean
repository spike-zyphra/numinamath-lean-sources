import Mathlib

open Real

theorem calculus_164437 : ∫ x in (1)..4, x^2 = 21 := by 
  norm_num [Finset.sum_range_succ, mul_comm]