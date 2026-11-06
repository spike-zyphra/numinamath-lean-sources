import Mathlib

theorem algebra_12875 :
    IsGreatest {n | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).prod = Nat.factorial 7} 98752 := by
  constructor
  · -- Show 98752 is in the set
    constructor
    · -- Show 98752 is in the range [10000, 99999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show the product of digits is 7!
      norm_num [Nat.factorial]
  · -- Show there is no greater element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1r⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.factorial] at hn2 <;> omega