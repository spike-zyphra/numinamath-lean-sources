import Mathlib

theorem number_theory_14175 :
    IsLeast {K : ℕ | 1 < K ∧ ∃ Z : ℕ, 500 < Z ∧ Z < 1000 ∧ Z = K * K ^ 2 ∧ ∃ m : ℕ, m ^ 2 = Z} 9 := by
  constructor
  · -- Show that 9 is in the set
    constructor
    · norm_num 
    · use 729 
      constructor
      · norm_num 
      constructor
      · norm_num 
      constructor
      · norm_num 
      · use 27
        all_goals norm_num
  · -- Show that 9 is the least such
    intro K h
    rcases h with ⟨h1, Z, h2, h3, h4, m, h5⟩
    by_contra h6
    push_neg at h6 
    have h7 : K ≤ 8 := by omega 
    have h8 : Z = K * K ^ 2 := by linarith 
    have h9 : m ^ 2 = Z := by linarith 
    have h10 : K ≤ 8 := h7 
    interval_cases K <;> try { 
      norm_num [h8] at h9 h2 h3 ⊢
      all_goals 
        try { 
          have : m ≤ 31 := by nlinarith 
          interval_cases m <;> omega 
        }
    }