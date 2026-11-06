import Mathlib

theorem algebra_21413 : ∑ n in Finset.range 3, (Nat.choose 12 (6 * n)) * (2 ^ (3 * (2 - n))) * (3 ^ (2 * n)) = 66673 := by 
  norm_num [Finset.sum_range_succ, Nat.choose]