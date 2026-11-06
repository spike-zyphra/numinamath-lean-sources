import Mathlib

theorem number_theory_4563 : IsLeast {x : ℤ | 0 < x ∧ 2018 * x % 2016 = 44} 22 := by 
  constructor
  · -- Show 22 is in the set
    constructor 
    · norm_num 
    · norm_num 
  · -- Show there is no smaller element in the set 
    intro x h 
    rcases h with ⟨hx_pos, hx_cong⟩ 
    by_contra h'
    push_neg at h'
    have h1 : x > 0 := hx_pos 
    have h2 : x < 22 := h'
    interval_cases x <;> norm_num at hx_cong <;> omega