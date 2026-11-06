import Mathlib

open Real

theorem calculus_156790 : ∫ x in (3)..1, x^2 = -26/3 := by 
  norm_num [Finset.sum_range_succ, mul_comm]