import Mathlib

theorem algebra_10732 : 2^10 - ∑ k in Finset.Icc 1 8, 2^k = 514 := by 
  norm_num [Finset.sum_Icc_succ_top]