import Mathlib

theorem algebra_3659 : ∑ i ∈ Finset.Icc 1 11, i * (i + 1) * (i + 2) = 6006 := by 
  norm_num [Finset.sum_Icc_succ_top]