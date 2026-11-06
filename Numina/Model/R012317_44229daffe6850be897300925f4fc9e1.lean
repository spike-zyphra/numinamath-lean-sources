import Mathlib

theorem algebra_47780 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a^3 - 3*a^2 - 7*a - 1 = 0) (h' : b^3 - 3*b^2 - 7*b - 1 = 0)
    (h'' : c^3 - 3*c^2 - 7*c - 1 = 0) :
    ∃ p q r : ℕ, p > 0 ∧ q > 0 ∧ r > 0 ∧ Nat.gcd p r = 1 ∧ ¬∃ p' : ℕ, p'^3 ∣ q ∧
      (1/(a^(1/3) - b^(1/3)) + 1/(b^(1/3) - c^(1/3)) +
       1/(c^(1/3) - a^(1/3)))^2 = p*(q^(1/3))/r := by
  use 1, 1, 1
  constructor
  · -- Show p > 0 
    norm_num 
  constructor
  · -- Show q > 0 
    norm_num 
  constructor 
  · -- Show r > 0 
    norm_num 
  constructor 
  · -- Show gcd(p, r) = 1 
    norm_num 
  · -- Show ¬∃ p' : ℕ, p'^3 ∣ q ∧ 
    intro h1 
    rcases h1 with ⟨p', hp1, heq⟩ 
    have hp2 : p' ^ 3 ∣ 1 := hp1 
    have hp3 : p' ^ 3 = 1 := by 
      have h1 : p' ^ 3 ∣ 1 := hp1 
      have h2 : p' ^ 3 ≤ 1 := by 
        apply Nat.le_of_dvd (by norm_num) h1 
      have h3 : p' ≤ 1 := by 
        by_contra h4 
        push_neg at h4 
        have h5 : p' ^ 3 > 1 := by 
          have hp6 : p' ≥ 2 := by linarith 
          have hp7 : p' ^ 3 ≥ 2 ^ 3 := by 
            apply Nat.pow_le_pow_of_le_left hp6 3 
          nlinarith 
        nlinarith 
      interval_cases p' <;> omega 
    have hp4 : p' = 1 := by 
      have h1 : p' ^ 3 = 1 := hp3 
      have h2 : p' = 1 := by 
        have h3 : p' ^ 3 = 1 := h1 
        have h4 : p' ≤ 1 := by 
          by_contra h5 
          push_neg at h5 
          have h6 : p' ^ 3 > 1 := by 
            have hp7 : p' ≥ 2 := by linarith 
            have hp8 : p' ^ 3 ≥ 2 ^ 3 := by 
              apply Nat.pow_le_pow_of_le_left hp7 3 
            nlinarith 
          nlinarith 
        interval_cases p' <;> omega 
      exact h2 
    norm_num [hp4] at hp1 hp3 
    norm_num at heq 
    all_goals 
      norm_num [sq_pos_of_ne_zero (show a - b ≠ 0 by intro heq4; apply ha; linarith), 
                sq_pos_of_ne_zero (show b - c ≠ 0 by intro heq4; apply hb; linarith), 
                sq_pos_of_ne_zero (show a - c ≠ 0 by intro heq4; apply hc; linarith)] at heq 
      all_goals 
        nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by intro heq4; apply ha; linarith), 
                  sq_pos_of_ne_zero (show b - c ≠ 0 by intro heq4; apply hb; linarith), 
                  sq_pos_of_ne_zero (show a - c ≠ 0 by intro heq4; apply hc; linarith)]