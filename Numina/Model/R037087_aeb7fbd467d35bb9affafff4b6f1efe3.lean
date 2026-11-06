import Mathlib

theorem number_theory_274765 :
    IsLeast {x | x % 2 = 1 ∧ x % 3 = 2 ∧ x % 4 = 3 ∧ x % 5 = 4 ∧ x % 6 = 5} 59 := by 
  constructor
  · -- Let's show that 59 satisfies all the conditions
    show 59 % 2 = 1 ∧ 59 % 3 = 2 ∧ 59 % 4 = 3 ∧ 59 % 5 = 4 ∧ 59 % 6 = 5
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Now we need to show that 59 is the least such number
    intro x hx
    rcases hx with ⟨h2, h3, h4, h5, h6⟩
    by_contra h
    push_neg at h
    have h7 : x < 59 := h
    interval_cases x <;> omega