import Mathlib

theorem number_theory_11171 : IsLeast {x : ℕ | 0 < x ∧ (x + 4609) % 12 = 2104 % 12} 3 := by 
  constructor
  · -- Show 3 is in the set
    constructor
    · -- Show 0 < 3
      norm_num
    · -- Show (3 + 4609) % 12 = 2104 % 12
      norm_num
  · -- Show 3 is the smallest
    intro y hy
    rcases hy with ⟨hy1, hy2⟩
    by_contra h
    push_neg at h
    have h1 : y < 3 := by
      omega
    interval_cases y <;> norm_num at hy2 <;> all_goals omega