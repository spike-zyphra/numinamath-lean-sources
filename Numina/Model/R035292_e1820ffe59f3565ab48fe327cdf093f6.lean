import Mathlib

theorem number_theory_256574 {n : ℕ} (hn : 2 ≤ n) :
    ∃ a b, a = n.minFac ∧ b ∣ n ∧ n = a^2 + b^2 ↔ n = 8 ∨ n = 20 := by
  by_cases h : n = 8 
  · -- Case n = 8
    use 2, 2 
    simp [h] 
    all_goals norm_num 
  · -- Case n ≠ 8
    by_cases h3 : n = 20
    · -- Case n = 20
      use 2, 4 
      simp [h3] 
      all_goals norm_num 
    · -- Now prove for any n not 8 or 20
      have h2 : n ≠ 8 := h 
      have h3 : n ≠ 20 := by 
        intro h4 
        tauto 
      use n.minFac, 0 
      simp at *
      <;> try { 
        all_goals 
        try { 
          tauto 
        } 
        <;> try { 
          all_goals 
          have h2 : ¬ (0 ∣ n) := by 
            intro h5 
            have h4 : n = 0 := by 
              omega 
            omega 
          tauto 
        }
      }