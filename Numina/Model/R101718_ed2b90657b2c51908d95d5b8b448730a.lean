import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_138657 :
  ∫ x in (0)..1, ∫ y in (x - x^2)..(1 - x^2), (x + 2 * y) = 2 / 3 := by
  norm_num [Finset.sum_range_succ, mul_comm]
  <;> ring_nf <;> norm_num