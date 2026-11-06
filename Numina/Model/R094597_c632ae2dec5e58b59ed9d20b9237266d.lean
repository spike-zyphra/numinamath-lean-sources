import Mathlib

theorem number_theory_5203 : IsGreatest {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ Nat.gcd n 1608 = 201} 9849 := by
  constructor
  · -- Show that 9849 is in the set
    constructor
    · -- Show that 9849 is in the range [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that gcd(9849, 1608) = 201
      norm_num [Nat.gcd]
  · -- Show that 9849 is the greatest element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1_lower, hn1_upper⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hn2 <;> all_goals omega