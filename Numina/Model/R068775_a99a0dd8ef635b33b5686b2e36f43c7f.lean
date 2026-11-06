import Mathlib

theorem number_theory_235491 :
    IsGreatest {n | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).prod = 2520} 98751 := by
  constructor
  · -- Show that 98751 belongs to the set
    constructor
    · -- Show that 98751 is in the range [10000, 99999]
      native_decide
    · -- Show that the product of the digits of 98751 equals 2520
      native_decide
  · -- Show that 98751 is the greatest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 <;> all_goals omega