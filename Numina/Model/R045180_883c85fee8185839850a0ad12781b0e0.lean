import Mathlib
theorem algebra_240729 : ∏ k ∈ (Finset.Icc 2 100 : Finset ℕ), (k ^ 3 - (1 : ℝ)) / (k ^ 3 + 1) > 2 / 3:= by
  norm_num [Finset.prod_Icc_succ_top]