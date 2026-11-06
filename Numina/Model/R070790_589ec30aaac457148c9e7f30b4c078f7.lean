import Mathlib

theorem number_theory_120795 :
    IsLeast {n | n ∈ Finset.Icc 10000 99999 ∧ 2014 ∣ n ∧ (n % 1000) ≠ 0 ∧ (n % 1000).divisors.card = 16} 24168 := by 
  constructor
  · -- Show 24168 is in the set
    constructor
    · -- Show 24168 is in the range [10000, 99999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 2014 divides 24168
      norm_num
    constructor
    · -- Show 24168 % 1000 ≠ 0
      norm_num
    · -- Show (24168 % 1000).divisors.card = 16
      native_decide
  · -- Show that for any n in the set, 24168 ≤ n
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h10, h99⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { all_goals contradiction }
    <;> try { contradiction }