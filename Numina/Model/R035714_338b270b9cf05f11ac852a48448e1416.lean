import Mathlib

theorem algebra_22041 : IsLeast {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).prod * 2 = n} 36 := by 
  constructor
  · -- Show that 36 is in the set
    constructor
    · -- Show that 36 is in the range [10, 99]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Verify that the product of digits is half of 36
      norm_num
  · -- Show that 36 is the smallest
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h10, h99⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 <;> all_goals contradiction