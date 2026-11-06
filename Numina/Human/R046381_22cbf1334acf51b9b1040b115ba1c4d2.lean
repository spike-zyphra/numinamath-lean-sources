import Mathlib

theorem calculus_156800 : ∫ x in (1)..2, (5 * x ^ 4 + 2 * x - 8) = 26 := by
  norm_num [Finset.sum_range_succ, mul_comm]