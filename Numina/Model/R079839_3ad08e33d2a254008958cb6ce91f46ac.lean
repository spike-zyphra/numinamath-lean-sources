import Mathlib

theorem algebra_5213 : ∑ i in Finset.Icc 6 25, i^2 = 5470 := by 
  norm_num [Finset.sum_Icc_succ_top, sq]