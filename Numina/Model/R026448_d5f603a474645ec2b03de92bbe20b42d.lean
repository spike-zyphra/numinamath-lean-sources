import Mathlib

theorem number_theory_62731 (p : ℕ) (hp : p.Prime) (h1 : (p ^ 2 - 6).Prime) (h2 : (p ^ 2 + 6).Prime) :
    p = 5 := by
  by_cases hp5 : p ≤ 5
  · interval_cases p <;> norm_num at *
    <;> try { contradiction }
    all_goals tauto
  · push_neg at hp5
    have h3 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      have h5 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        by_contra h 
        push_neg at h 
        have h6 : p % 5 = 0 := by
          omega 
        have h7 : p ≠ 5 := by 
          nlinarith 
        have h8 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by 
            omega 
          ) (by nlinarith) (by nlinarith) 
        contradiction 
      assumption 
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- p % 5 = 1 
      have hp21 : p ^ 2 % 5 = 1 := by 
        simp [Nat.pow_mod, h3]
      have h4 : (p ^ 2 - 6) % 5 = 0 := by 
        omega 
      have h8 : ¬ (p ^ 2 - 6).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (p ^ 2 - 6) by 
          omega 
        ) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 - 6 ≥ 5 := by 
            omega 
          all_goals omega 
        }) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 - 6 ≥ 5 := by 
            omega 
          all_goals omega 
        }) 
      contradiction 
    · -- p % 5 = 2 
      have hp24 : p ^ 2 % 5 = 4 := by 
        simp [Nat.pow_mod, h3]
      have h4 : (p ^ 2 + 6) % 5 = 0 := by 
        omega 
      have h8 : ¬ (p ^ 2 + 6).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (p ^ 2 + 6) by 
          omega 
        ) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 + 6 ≥ 11 := by 
            omega 
          all_goals omega 
        }) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 + 6 ≥ 11 := by 
            omega 
          all_goals omega 
        }) 
      contradiction 
    · -- p % 5 = 3 
      have hp24 : p ^ 2 % 5 = 4 := by 
        simp [Nat.pow_mod, h3]
      have h4 : (p ^ 2 + 6) % 5 = 0 := by 
        omega 
      have h8 : ¬ (p ^ 2 + 6).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (p ^ 2 + 6) by 
          omega 
        ) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 + 6 ≥ 11 := by 
            omega 
          all_goals omega 
        }) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 + 6 ≥ 11 := by 
            omega 
          all_goals omega 
        }) 
      contradiction 
    · -- p % 5 = 4 
      have hp21 : p ^ 2 % 5 = 1 := by 
        simp [Nat.pow_mod, h3]
      have h4 : (p ^ 2 - 6) % 5 = 0 := by 
        omega 
      have h8 : ¬ (p ^ 2 - 6).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (p ^ 2 - 6) by 
          omega 
        ) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 - 6 ≥ 5 := by 
            omega 
          all_goals omega 
        }) (by {
          have h11 : p ≥ 6 := by linarith 
          have h12 : p ^ 2 ≥ 36 := by nlinarith [h11] 
          have h13 : p ^ 2 - 6 ≥ 5 := by 
            omega 
          all_goals omega 
        }) 
      contradiction