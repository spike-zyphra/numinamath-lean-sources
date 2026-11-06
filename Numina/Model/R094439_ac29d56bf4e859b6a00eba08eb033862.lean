import Mathlib

theorem algebra_289705 : ∑ n in Finset.Icc 1 20, n = 210 := by 
  norm_num [Finset.sum_Icc_succ_top]