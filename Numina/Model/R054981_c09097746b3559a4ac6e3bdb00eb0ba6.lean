import Mathlib

open Real
open scoped BigOperators

theorem number_theory_178398 :
  ⌊4 * ∑ i ∈ Finset.range 2011, (1 / (i + 1)^3 : ℝ)⌋ = 4 := by
  norm_num [Finset.sum_range_succ]