import Mathlib

theorem number_theory_11979 : IsGreatest {n : ℕ+ | n < 1000 ∧ (Nat.digits 10 n.val).sum = (Nat.digits 2 n.val).sum} 503 := by
  constructor 
  · -- Show 503 is in the set
    constructor
    · norm_num
    · native_decide
  · -- Show there is no greater element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h 
    push_neg at h 
    have h1 : n.val > 503 := by 
      exact_mod_cast h
    have h2 : n.val < 1000 := by 
      exact_mod_cast hn1
    interval_cases h : n.val <;> norm_num at h1 h2 hn2 ⊢ <;> norm_num [Nat.succ, Nat.add_comm] at hn2 ⊢