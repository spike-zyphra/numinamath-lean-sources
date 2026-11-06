import Mathlib

theorem number_theory_7116 (S : Finset ℕ) (hS : S = {2, 3, 12, 14, 15, 20, 21}) :
    ∃ T ⊆ S, T.card = 3 ∧ ∏ i ∈ T, i = 2520 := by 
  use {12, 14, 15}
  simp [Finset.subset_iff, hS]
  all_goals
    native_decide