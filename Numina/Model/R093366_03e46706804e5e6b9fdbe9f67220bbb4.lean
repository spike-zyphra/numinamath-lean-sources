import Mathlib

theorem number_theory_200024 : (∑ i ∈ Finset.Icc 1 6, i^6) % 7 = 6 := by 
  norm_num [Finset.sum_Icc_succ_top]