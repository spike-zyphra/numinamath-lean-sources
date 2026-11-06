import Mathlib

theorem number_theory_250848 :
    IsLeast {n | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).length = 3 ∧ (Nat.digits 10 n).toFinset.card = 3 ∧ n.divisors.card = 3} 169 := by 
  constructor
  · -- Show that 169 is in the set
    constructor
    · -- Show 169 ∈ [100, 999]
      simp [Finset.mem_Icc]
    constructor
    · -- Show the digits length is 3
      norm_num
    constructor
    · -- Show all digits are different
      native_decide
    · -- Show the number of divisors is 3
      native_decide
  · -- Show that 169 is the smallest
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }
    <;> norm_num at *
    <;> try native_decide
    <;> try tauto