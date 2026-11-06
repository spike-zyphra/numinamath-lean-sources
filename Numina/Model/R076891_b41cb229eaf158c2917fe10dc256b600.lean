import Mathlib

theorem number_theory_308510 (p : ℕ) (hp : p.Prime) (h8p2 : (8 * p ^ 2 + 1).Prime) :
    p = 3 := by 
  -- Assume p is a prime and 8p^2 + 1 is also a prime
  -- Let's consider the case where p > 3
  by_cases h : p ≤ 3
  · -- If p ≤ 3 (p can be 2 or 3 since it's prime)
    interval_cases p <;> norm_num at hp h8p2 ⊢ <;> trivial 
  · -- Case p > 3 
    -- Assume p > 3. Then p must be congruent to 1 or 2 modulo 3
    have h2 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by 
      omega 
    rcases h2 with (h2 | h2 | h2)
    · -- p % 3 = 0
      have h3 : p % 3 = 0 := by 
        omega 
      have h4 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega 
      contradiction 
    · -- p % 3 = 1
      have h3 : p % 3 = 1 := by 
        omega 
      have h5 : (8 * p ^ 2 + 1) % 3 = 0 := by 
        have h6 : p % 3 = 1 := h3 
        have h7 : p ^ 2 % 3 = 1 := by 
          norm_num [Nat.pow_mod, h6] 
        omega 
      have h6 : ¬ (8 * p ^ 2 + 1).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p ^ 2 + 1) by omega)
        all_goals 
          nlinarith 
        all_goals 
          nlinarith 
      contradiction 
    · -- p % 3 = 2 
      have h3 : p % 3 = 2 := by 
        omega 
      have h5 : (8 * p ^ 2 + 1) % 3 = 0 := by 
        have h6 : p % 3 = 2 := h3 
        have h7 : p ^ 2 % 3 = 1 := by 
          norm_num [Nat.pow_mod, h6] 
        omega 
      have h6 : ¬ (8 * p ^ 2 + 1).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p ^ 2 + 1) by omega)
        all_goals 
          nlinarith 
        all_goals 
          nlinarith 
      contradiction