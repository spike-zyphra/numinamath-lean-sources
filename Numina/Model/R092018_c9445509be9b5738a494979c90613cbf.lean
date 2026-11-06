import Mathlib

theorem algebra_13949 :
    IsLeast {n | n ∈ Finset.Icc 1000 9999 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 4 ∣ n} 2112 := by
  constructor
  · -- Show that 2112 is in the set
    constructor
    · -- Show that 2112 ∈ [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 2112 is a palindrome
      native_decide
    · -- Show that 2112 is divisible by 4
      norm_num
  · -- Show that 2112 is the smallest
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 hn3 ⊢ <;> try { norm_num [Nat.digits, Nat.digitsAux] at hn2; all_goals contradiction }