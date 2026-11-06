import Mathlib

theorem number_theory_239232 : IsGreatest {x | x ≠ 0 ∧ 845 % x = 5 ∧ 275 % x = 5} 30 := by
  constructor
  · -- Show 30 is in the set 
    constructor
    · -- Show 30 ≠ 0 
      norm_num
    constructor
    · -- Show 845 % 30 = 5 
      norm_num
    · -- Show 275 % 30 = 5 
      norm_num
  · -- Show that for any x in the set, x ≤ 30 
    intro x
    intro h 
    rcases h with ⟨hx1, hx2, hx3⟩
    by_contra h'
    push_neg at h'
    have h4 : x > 0 := by 
      by_contra h'
      push_neg at h'
      have : x ≤ 0 := by omega 
      have h'2 : x = 0 := by linarith
      contradiction 
    have h5 : x ≤ 275 := by
      by_contra h6
      push_neg at h6
      have h7 : x > 275 := h6
      have h8 : 275 % x = 275 := by
        rw [Nat.mod_eq_of_lt]
        linarith 
      omega 
    have h5 : x ≤ 845 := by
      by_contra h6
      push_neg at h6
      have h7 : x > 845 := h6
      have h8 : 845 % x = 845 := by
        rw [Nat.mod_eq_of_lt]
        linarith 
      omega 
    interval_cases x <;> norm_num at hx1 hx2 hx3 ⊢ <;> omega