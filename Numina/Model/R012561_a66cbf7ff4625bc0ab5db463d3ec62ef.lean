import Mathlib

theorem number_theory_217632 (a b c d : ℕ) (h₀ : a < 10) (h₁ : b < 10) (h₂ : c < 10) (h₃ : d < 10)
    (h₄ : a + b + c + d = 26) (h₅ : (b * d) / 10 = (a + c)) (h₆ : ∃ k, b * d - c ^ 2 = 2 ^ k) :
    1000 * a + 100 * b + 10 * c + d = 1979 := by 
  have h7 : b + d = 18 := by 
    have h8 : a + c ≤ 8 := by
      have h9 : b * d ≤ 81 := by 
        interval_cases b <;> interval_cases d <;> omega 
      omega 
    omega 
  have h8 : b = 9 := by 
    omega 
  have h9 : d = 9 := by 
    omega 
  have h10 : a + c = 8 := by 
    norm_num [h8, h9] at h₅ 
    omega 
  rcases h₆ with ⟨k, hk⟩ 
  have h11 : b * d = 81 := by 
    nlinarith [h8, h9] 
  have eq1 : 81 - c ^ 2 = 2 ^ k := by
    have h12 : b * d = 81 := h11 
    have eq2 : b * d - c ^ 2 = 2 ^ k := by 
      linarith [hk, h12] 
    omega 
  have h14 : c ≤ 9 := by 
    linarith 
  interval_cases c <;> try { 
    omega 
  } 
  <;> try { 
    norm_num at eq1 
    all_goals 
      have : k ≤ 30 := by 
        by_contra h 
        push_neg at h 
        have h15 : 2 ^ k ≥ 2 ^ 31 := by 
          have : k ≥ 31 := by 
            omega 
          have h16 : 2 ^ k ≥ 2 ^ 31 := by 
            apply Nat.pow_le_pow_of_le_right 
            all_goals 
              omega 
          linarith 
        omega 
      interval_cases k <;> omega 
  }