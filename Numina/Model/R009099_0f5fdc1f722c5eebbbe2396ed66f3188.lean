import Mathlib

theorem algebra_14920 : ∏ n ∈ Finset.Icc (1 : ℕ) 13, (n * (n + 2) / (n + 4)^2 : ℚ) = 3 / 161840 := by
  norm_num [Finset.prod_Icc_succ_top]