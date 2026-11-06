import Mathlib

open Real

theorem algebra_1708 : round ((∑ i in (Finset.range 1001), ((i + 1)^2 / (2 * i + 1)) : ℝ) -
(∑ i in (Finset.range 1001), ((i + 1)^2 / (2 * i + 3)) : ℝ)) = 501 := by
  norm_num [Finset.sum_range_succ, round_eq]
  <;> norm_num
  <;> linarith