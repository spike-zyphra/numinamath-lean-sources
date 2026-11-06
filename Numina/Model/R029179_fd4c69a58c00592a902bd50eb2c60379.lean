import Mathlib

open Real

theorem negated_inequalities_72307 : ∏ i ∈ Finset.range 1009, (1 + 1 / (2 * i + 2 : ℝ)) < 50 := by 
  norm_num [Finset.prod_range_succ]