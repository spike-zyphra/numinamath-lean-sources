import Mathlib

theorem number_theory_280019 :
    IsLeast {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n).toFinset.card = 4} 1023 := by 
  constructor
  · -- Show 1023 is in the set
    constructor
    · -- Show 1023 ∈ [1000, 9999]
      native_decide 
    constructor
    · -- Show (Nat.digits 10 1023).length = 4
      native_decide 
    · -- Show (Nat.digits 10 1023).toFinset.card = 4
      native_decide 
  · -- Prove that 1023 is a lower bound
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1 
    by_contra h
    push_neg at h 
    interval_cases n <;> norm_num at hn2 hn3 <;> all_goals contradiction