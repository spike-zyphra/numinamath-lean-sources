import Mathlib

theorem number_theory_65611 : IsGreatest {k | 2 ^ k ∣ ∏ i ∈ Finset.Icc 2008 4014, i} 2007 := by 
  constructor
  · -- We verify that 2007 is in the divisibility set
    native_decide
  · -- We verify that all elements in the divisibility set are at most 2007
    intro k
    intro fours
    have imp : 2 ^ k ∣ ∏ i ∈ Finset.Icc 2008 4014, i := by 
      simpa using fours
    by_contra hf
    push_neg at hf
    have imp1 : k > 2007 := by
      omega
    have imp2 : k ≥ 2008 := by
      omega
    have imp3 : ¬(2 ^ 2008 ∣ ∏ i ∈ Finset.Icc 2008 4014, i) := by 
      native_decide
    have imp4 : 2 ^ 2008 ∣ 2 ^ k := by
      apply pow_dvd_pow _ (by omega)
    have imp5 : 2 ^ 2008 ∣ ∏ i ∈ Finset.Icc 2008 4014, i := by
      exact dvd_trans imp4 imp
    exact imp3 imp5