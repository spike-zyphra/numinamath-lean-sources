import Mathlib

theorem number_theory_5373 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ Nat.gcd n 2496 = 312} 9672 := by 
  constructor
  · -- Show that 9672 is in the set
    constructor
    · -- Show that 9672 is in the range [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that gcd(9672, 2496) = 312
      norm_num [Nat.gcd]
  · -- Show that for all n in the set, n ≤ 9672
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn11, hn12⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hn2 ⊢ <;> omega