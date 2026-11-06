import Mathlib

theorem number_theory_7718 (p : ℕ) (hp : p.Prime) :
    ∃ k, k^2 = p^3 - 4 * p + 9 ↔ p = 2 ∨ p = 7 ∨ p = 11 := by
  by_cases h1 : p ≤ 11
  · -- p ≤ 11
    have h2 : p ≤ 11 := h1
    interval_cases p <;> norm_num at hp ⊢ <;> try { 
      use 3 
      all_goals norm_num 
    } <;> try { 
      use 18 
      all_goals norm_num 
    } <;> try { 
      use 36 
      all_goals norm_num 
    } <;> try { 
      use 0 
      all_goals norm_num 
    }
  · -- p > 11
    use 0 
    constructor 
    · -- Assume k^2 = p^3 - 4 * p + 9, prove p = 2 ∨ p = 7 ∨ p = 11
      intro h_eq 
      have h3 : p > 11 := by omega 
      have h4 : p ^ 3 - 4 * p + 9 > 0 := by 
        have h5 : p ≥ 12 := by omega 
        have h6 : p ^ 3 ≥ 12 ^ 3 := by 
          have h7 : p ≥ 12 := by omega 
          have h8 : p ^ 3 ≥ 12 ^ 3 := by 
            apply Nat.pow_le_pow_of_le_left 
            all_goals 
              omega 
          linarith 
        have h7 : 4 * p ≤ 4 * p := by omega 
        omega 
      omega 
    · -- Assume p = 2 ∨ p = 7 ∨ p = 11, prove k^2 = p^3 - 4 * p + 9 
      rintro (h_eq | h_eq | h_eq)
      all_goals 
        omega