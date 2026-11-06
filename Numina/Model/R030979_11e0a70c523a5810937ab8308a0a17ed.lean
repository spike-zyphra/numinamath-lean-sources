import Mathlib

theorem number_theory_213434 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n).toFinset.card = 4 ∧ 2 ∣ n ∧ 5 ∣ n ∧ 9 ∣ n ∧ 11 ∣ n} 8910 := by
  constructor
  · -- Show 8910 is in the set
    constructor
    · -- Show that 8910 is in the range [1000, 9999]
      native_decide
    constructor
    · -- Show that the length of the digits is 4
      native_decide
    constructor
    · -- Show that the cardinality of the digit set is 4
      native_decide
    constructor
    · -- Show that 2 divides 8910
      norm_num
    constructor
    · -- Show that 5 divides 8910
      norm_num
    constructor
    · -- Show that 9 divides 8910
      norm_num
    · -- Show that 11 divides 8910
      norm_num
  · -- Show that for any n in the set, n ≤ 8910
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, h2, h5, h9, h11⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 8911 := by omega
    interval_cases n <;> norm_num at h2 h5 h9 h11 hn2 hn3 <;> all_goals
      contradiction