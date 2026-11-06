import Mathlib

theorem number_theory_179141 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ 7 ∣ n ∧ (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n).toFinset.card = 4} 9870 := by
  constructor
  · -- Let's verify that 9870 belongs to our set.
    constructor
    · -- Show that 9870 ∈ [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 7 divides 9870
      norm_num
    constructor
    · -- Show that the length of digits is 4
      norm_num
    · -- Show that the set of digits has 4 elements
      native_decide
  · -- Assume n is in the set, we need to show n ≤ 9870
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 hn3 hn4 <;> try { exfalso } <;> try { tauto } <;> try { contradiction }