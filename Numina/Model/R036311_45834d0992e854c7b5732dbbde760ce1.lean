import Mathlib

theorem number_theory_26059 :
    IsGreatest {n | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum ∣ n} 99972 := by
  constructor
  · -- Show 99972 is in the set
    constructor
    · -- Show 99972 is in the range [10000, 99999]
      simp [Finset.mem_Icc]
    · -- Show that the sum of the digits of 99972 divides 99972
      norm_num
  · -- Show it's greatest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 ⊢ <;> omega