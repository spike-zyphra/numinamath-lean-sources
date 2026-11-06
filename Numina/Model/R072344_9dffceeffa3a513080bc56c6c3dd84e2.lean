import Mathlib

theorem number_theory_12394 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, k^2 = 4 * n + 1 ∧ ∃ m, m^2 = 6 * n + 1} 20 := by 
  constructor
  · -- Show 20 is in the set
    constructor
    · -- Show 20 > 0
      norm_num 
    · -- Show existence of k 
      use 9 
      constructor
      · -- Show k^2 = 4 * 20 + 1
        norm_num 
      · -- Show existence of m 
        use 11 
        all_goals norm_num 
  · -- Show that 20 is the minimal
    intro n hn 
    rcases hn with ⟨hn_pos, k, hk_eq, m, hm_eq⟩
    by_contra h 
    push_neg at h 
    have h1 : k ≤ 9 := by 
      nlinarith 
    have h2 : m ≤ 11 := by 
      nlinarith 
    interval_cases n <;> 
      try { 
        interval_cases k <;> 
        interval_cases m <;> 
        all_goals 
          norm_num at hk_eq hm_eq <;> 
          all_goals 
            omega 
      }