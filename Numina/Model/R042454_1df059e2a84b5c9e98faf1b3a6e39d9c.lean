import Mathlib

theorem number_theory_144333 :
    IsLeast {x | ∃ n, x = 15 * n + 2 ∧ ∃ m, x = 28 * m + 8} 92 := by
  constructor
  · -- Show 92 is in the set
    use 6
    constructor
    · norm_num 
    · use 3
      all_goals norm_num 
  · -- Show no smaller element is in the set
    intro x hx
    rcases hx with ⟨n, h1, m, h2⟩
    by_contra h
    push_neg at h
    have h3 : 15 * n + 2 < 92 := by
      linarith 
    have h4 : 28 * m + 8 < 92 := by
      linarith 
    have h5 : n < 6 := by 
      omega
    have h6 : m < 3 := by 
      omega
    interval_cases n <;> interval_cases m
    all_goals 
      omega