import Mathlib

theorem number_theory_3747 : ∑ x ∈ Finset.Icc 1 10, x^0 = 10 := by
  norm_num [Finset.sum_Icc_succ_top]