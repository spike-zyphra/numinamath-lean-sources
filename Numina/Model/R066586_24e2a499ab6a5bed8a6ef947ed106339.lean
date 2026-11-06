import Mathlib

theorem algebra_22132 {n : ℕ} (hn : n = 12) :
    ∑ i ∈ Finset.Icc 1 n, i = 78 := by 
  subst hn
  norm_num [Finset.sum_Icc_succ_top]