import Mathlib

theorem number_theory_11870 : ∑ x in (Finset.Ico 1 100).filter (fun y => Nat.Coprime y 100), (x / 100 : ℝ) = 20 := by
  norm_num [Finset.sum_filter, Finset.sum_Ico_succ_top]