import Mathlib

theorem number_theory_255781 : IsGreatest {x | x ∣ 1001001001 ∧ x < 10000} 9901 := by 
  constructor
  · -- Prove that 9901 is in the set 
    constructor
    · -- Show that 9901 divides 1001001001
      norm_num
    · -- Show that 9901 < 10000
      norm_num
  · -- Prove that 9901 is greatest such divisor 
    intro x h
    rcases h with ⟨hdiv, hx⟩
    by_contra h'
    push_neg at h'
    interval_cases x <;> norm_num at hdiv hx <;> omega