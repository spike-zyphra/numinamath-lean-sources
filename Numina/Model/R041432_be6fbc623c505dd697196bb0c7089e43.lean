import Mathlib

theorem number_theory_115077 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h : 15 * a + 35 * b + 91 * c = 2015) :
    a = 97 ∧ b = 3 ∧ c = 5 := by

  have h1 : c % 5 = 0 := by
    omega

  have h2 : c = 5 := by
    by_cases h3 : c > 5
    · -- c > 5
      have h4 : c % 5 = 0 := h1
      have h5 : ¬c.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ c by omega)
        all_goals 
          omega
      contradiction
    · -- c ≤ 5
      interval_cases c <;> norm_num at hc <;> try { tauto }

  rw [h2] at h

  have h3 : 15 * a + 35 * b = 1560 := by 
    omega

  have h4 : 3 * a + 7 * b = 312 := by 
    omega

  have h5 : b % 3 = 0 := by 
    omega

  have h6 : b = 3 := by 
    by_cases h7 : b > 3
    · -- b > 3
      have h8 : b % 3 = 0 := h5
      have h9 : ¬b.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ b by omega)
        all_goals 
          omega
      contradiction
    · -- b ≤ 3
      interval_cases b <;> norm_num at hb <;> try { tauto }

  rw [h6] at h4
  have h7 : 3 * a = 291 := by 
    omega

  have h8 : a = 97 := by 
    omega

  exact ⟨h8, h6, h2⟩