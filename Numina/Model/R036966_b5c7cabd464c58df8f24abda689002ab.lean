import Mathlib

theorem number_theory_173871 (P1 P2 P3 : ℕ) (hP1 : P1.Prime) (hP2 : P2.Prime) (hP3 : P3.Prime)
    (hP23 : P2 > P3) (h : P1 * (P2 + P3) = 165) :
    (P1, P2, P3) = (3, 53, 2) ∨ (P1, P2, P3) = (5, 31, 2) ∨ (P1, P2, P3) = (11, 13, 2) := by
  have h1 : P1 ∣ 165 := by
    use P2 + P3
    linarith
  have h2 : P1 ≤ 165 := by
    exact Nat.le_of_dvd (by norm_num) h1
  have h3 : P1 = 3 ∨ P1 = 5 ∨ P1 = 11 := by
    interval_cases P1 <;> norm_num at hP1 h1 <;> try { tauto }
  rcases h3 with (h3 | h3 | h3)
  · -- P1 = 3 
    have eq1 : 3 * (P2 + P3) = 165 := by
      rw [h3] at h 
      all_goals linarith
    have eq2 : P2 + P3 = 55 := by
      omega
    have h5 : P3 = 2 := by
      by_cases h3 : P3 > 2 
      · -- P3 > 2 
        by_cases h4 : P3 % 2 = 0 
        · -- P3 is even 
          exfalso 
          have h7 : ¬ P3.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P3 by omega) (by omega) (by omega)
          contradiction 
        · -- P3 is odd 
          have h4 : P3 % 2 = 1 := by omega 
          have h5 : P2 % 2 = 0 := by 
            omega 
          have h6 : P2 = 2 := by 
            by_cases h7 : P2 > 2 
            · -- P2 > 2 
              exfalso 
              have h7 : ¬ P2.Prime := by 
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P2 by omega) (by omega) (by omega)
              contradiction 
            · -- P2 <= 2 
              interval_cases P2 <;> try { tauto } 
          omega 
      · -- P3 <= 2 
        interval_cases P3 <;> try { 
          norm_num at eq2 
          all_goals 
            try { 
              have h6 : P2 < 56 := by omega 
              interval_cases P2 <;> norm_num at hP2 hP3 eq2 <;> tauto 
            } 
        }
    have h8 : P2 = 53 := by 
      omega 
    left 
    simp [h3, h8, h5] 
  · -- P1 = 5 
    have eq1 : 5 * (P2 + P3) = 165 := by 
      rw [h3] at h 
      all_goals linarith 
    have eq2 : P2 + P3 = 33 := by 
      omega 
    have h5 : P3 = 2 := by 
      by_cases h3 : P3 > 2 
      · -- P3 > 2 
        by_cases h4 : P3 % 2 = 0 
        · -- P3 is even 
          exfalso 
          have h7 : ¬ P3.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P3 by omega) (by omega) (by omega)
          contradiction 
        · -- P3 is odd 
          have h4 : P3 % 2 = 1 := by omega 
          have h5 : P2 % 2 = 0 := by 
            omega 
          have h6 : P2 = 2 := by 
            by_cases h7 : P2 > 2 
            · -- P2 > 2 
              exfalso 
              have  h7 : ¬ P2.Prime := by 
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P2 by omega) (by omega) (by omega)
              contradiction 
            · -- P2 <= 2 
              interval_cases P2 <;> try { tauto } 
          omega 
      · -- P3 <= 2 
        interval_cases P3 <;> try { 
          norm_num at eq2 
          all_goals 
            try { 
              have h6 : P2 < 34 := by omega 
              interval_cases  P2 <;> norm_num at hP2 hP3 eq2 <;> tauto 
            } 
        }
    have h6 : P2 = 31 := by 
      omega 
    right 
    left 
    simp [h3, h6, h5] 
  · -- P1 = 11 
    have eq1 : 11 * (P2 + P3) = 165 := by 
      rw [h3] at h 
      all_goals linarith 
    have eq2 : P2 + P3 = 15 := by 
      omega 
    have h5 : P3 = 2 := by 
      by_cases h3 : P3 > 2 
      · -- P3 > 2 
        by_cases h4 : P3 % 2 = 0 
        · --  P3 is even 
          exfalso 
          have h7 : ¬ P3.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P3 by omega) (by omega) (by omega)
          contradiction 
        · -- P3 is odd 
          have h4 : P3 % 2 = 1 := by omega 
          have h5 : P2 % 2 = 0 := by 
            omega 
          have h6 : P2 = 2 := by 
            by_cases h7 : P2 > 2 
            · -- P2 > 2 
              exfalso 
              have h7 : ¬ P2.Prime := by 
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P2 by omega) (by omega) (by omega)
              contradiction 
            · -- P2 <= 2 
              interval_cases P2 <;> try { tauto } 
          omega 
      · -- P3 <= 2 
        interval_cases P3 <;> try { 
          norm_num at eq2 
          all_goals 
            try { 
              have h6 : P2 < 16 := by omega 
              interval_cases P2 <;> norm_num at hP2 hP3 eq2 <;> tauto 
            } 
        }
    have h6 : P2 = 13 := by 
      omega 
    right 
    right 
    simp [h3, h6, h5]