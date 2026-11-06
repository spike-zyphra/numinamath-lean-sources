import Mathlib

theorem number_theory_136004 (m : ℕ) (hm : m.Prime) (h : (m^2 + 2).Prime) :
    (m^3 + 2).Prime := by
  by_cases h1 : m ≤ 5
  · interval_cases m <;> norm_num at hm h ⊢ <;> try { tauto }
  · -- m > 5
    have h2 : m % 3 = 1 ∨ m % 3 = 2 := by
      by_contra h3
      push_neg at h3
      have h4 : m % 3 = 0 := by 
        omega
      have h5 : ¬ m.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ m by omega) 
        all_goals 
          nlinarith
      contradiction 
    have h3 : m % 3 = 1 ∨ m % 3 = 2 := h2
    rcases h3 with (h3 | h3)
    · have h4 : (m ^ 2 + 2) % 3 = 0 := by
        have h5 : m % 3 = 1 := h3
        have h6 : m ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, h5]
        omega
      have h9 : ¬ (m ^ 2 + 2).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (m ^ 2 + 2) by omega) 
        all_goals 
          nlinarith [show m ≥ 6 by omega, show m ^ 2 + 2 ≥ 3 by nlinarith]
      contradiction
    · have h4 : (m ^ 2 + 2) % 3 = 0 := by
        have h5 : m % 3 = 2 := h3
        have h6 : m ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, h5]
        omega
      have h9 : ¬ (m ^ 2 + 2).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (m ^ 2 + 2) by omega) 
        all_goals 
          nlinarith [show m ≥ 6 by omega, show m ^ 2 + 2 ≥ 3 by nlinarith]
      contradiction