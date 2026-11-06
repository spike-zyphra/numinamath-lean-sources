import Mathlib

theorem number_theory_322559 (p : ℕ) (hp : Nat.Prime p) (h : Nat.Prime (p^3 + 3)) :
    (p^33 + 33) % 10 = 5 := by
  by_cases h2 : p > 2
  · -- Assume p > 2, then p must be odd
    have hp1 : p % 2 = 1 := by 
      by_contra h
      push_neg at h
      have hp8' : p % 2 = 0 := by 
        omega 
      have hp5 : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega) 
      tauto 
    have hp11 : (p ^ 3 + 3) % 2 = 0 := by
      have hp1' : p % 2 = 1 := hp1 
      have h311 : p ^ 3 % 2 = 1 := by 
        simp [Nat.pow_mod, hp1']
      omega 
    have h4 : p ≥ 3 := by 
      by_contra h
      push_neg at h
      have hp5 : p < 3 := by linarith 
      interval_cases p <;> norm_num at hp h2
    have h6 : p ^ 3 + 3 > 2 := by 
      have h7 : p ≥ 3 := h4 
      have : p ^ 3 ≥ 27 := by 
        have : p ≥ 3 := h7 
        have h6' : p ^ 3 ≥ 3 ^ 3 := by 
          apply Nat.pow_le_pow_of_le_left 
          omega 
        have h8' : 3 ^ 3 = 27 := by norm_num 
        linarith [h8'] 
      linarith 
    have h7 : ¬Nat.Prime (p^3 + 3) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p^3 + 3) by omega) 
      all_goals 
      omega 
    contradiction
  · -- Assume p ≤ 2, then p must be 0, 1 or 2
    interval_cases p
    · -- p = 0, contradiction 
      norm_num at hp 
    · -- p = 1, contradiction 
      norm_num at hp 
    · -- p = 2 
      norm_num