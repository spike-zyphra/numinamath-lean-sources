import Mathlib

theorem number_theory_97356 :
IsGreatest {n : ℕ | n ∈ Set.Icc 100 999 ∧ ¬(∑ i in Finset.Icc 1 n, i ∣ ∏ i in Finset.Icc 1 n, i)} 996 := by
  constructor
  · -- Show 996 is in the set
    constructor
    · -- Show 996 is in the range [100, 999]
      norm_num [Set.mem_Icc]
    · -- Show the sum from 1 to 996 does not divide the product from 1 to 996
      native_decide
  · -- Show that for all n in the set, n ≤ 996
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rcases hn1 with ⟨hn3, hn4⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 997 := by omega
    have h2 : ∑ i in Finset.Icc 1 n, i ∣ ∏ i in Finset.Icc 1 n, i := by
      have h3 : n ≤ 999 := by omega
      interval_cases n <;> native_decide
    contradiction