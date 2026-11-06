import Mathlib

open Real
open scoped BigOperators

theorem algebra_26256 :
  ∃ n : ℕ, ∑ i in Finset.range (n + 1), (1 : ℝ) / (n.choose i) < 2.022 := by 
  use 0
  norm_num [Finset.sum_range_succ, Nat.choose_zero_right]