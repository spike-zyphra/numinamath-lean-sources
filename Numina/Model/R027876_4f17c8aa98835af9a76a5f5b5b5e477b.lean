import Mathlib

theorem number_theory_12199 :
    IsGreatest {n | n ∈ Finset.Icc 10000 99999 ∧ n % 6 = 0 ∧ (Nat.digits 10 n).length = 5 ∧ (Nat.digits 10 n).toFinset = {3, 4, 6, 8, 9}} 98634 := by
  constructor
  · -- Prove that 98634 is in the set
    constructor
    · -- Show 98634 is within the range [10000, 99999]
      native_decide
    constructor
    · -- Show 98634 % 6 = 0
      norm_num
    constructor
    · -- Show that the length of digits is 5
      native_decide
    · -- Show that the finset of digits is {3, 4, 6, 8, 9}
      native_decide
  · -- Prove that 98634 is greatest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 hn3 hn4 ⊢ <;> try { contradiction }