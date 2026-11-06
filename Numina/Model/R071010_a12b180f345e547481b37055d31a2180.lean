import Mathlib

theorem number_theory_288906 :
    IsLeast {k | 10 ≤ k ∧ ∃ m, m^2 = 45 * k} 20 := by
  constructor
  · -- First, let's show 20 is in the set
    constructor
    · norm_num
    · -- Show there exists m such that m^2 = 45 * 20
      use 30
      norm_num
  · -- Now, we need to show that 20 is the smallest such k
    intro k hk
    rcases hk with ⟨hk10, m, hm⟩
    by_contra h
    push_neg at h
    have h1 : k < 20 := h
    have h2 : m ≤ 30 := by nlinarith
    interval_cases k <;> 
      try { 
        interval_cases m <;> omega 
      }