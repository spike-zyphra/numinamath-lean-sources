import Mathlib

open Real
open scoped BigOperators

theorem algebra_309835 : ⌊4 * ∑ i ∈ Finset.range 99, (1 / (i + 1)^3 : ℝ)⌋ = 4 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]