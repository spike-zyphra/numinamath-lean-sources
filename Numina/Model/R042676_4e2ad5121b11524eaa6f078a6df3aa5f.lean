import Mathlib

theorem number_theory_264725 :
    IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ 3 ∣ ∑ i ∈ Finset.Icc 1 n, i^(i + 1)} 997 := by
  constructor
  · -- Show 997 is in the set.
    constructor
    · -- Show 997 ∈ Finset.Icc 100 999
      native_decide
    · -- Show 3 divides the sum up to 997
      native_decide
  · -- Show that for any n in the set, n ≤ 997
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n ≥ 998 := by
      omega
    have h4 : n ≤ 999 := by
      omega
    have h5 : n = 998 ∨ n = 999 := by
      omega
    rcases h5 with (r | r)
    · -- n = 998
      rw [r] at hn2
      have h998 : ¬ (3 ∣ ∑ i in Finset.Icc 1 998, i ^ (i + 1)) := by
        native_decide
      exact h998 hn2
    · -- n = 999
      rw [r] at hn2
      have h999 : ¬ (3 ∣ ∑ i in Finset.Icc 1 999, i ^ (i + 1)) := by
        native_decide
      exact h999 hn2