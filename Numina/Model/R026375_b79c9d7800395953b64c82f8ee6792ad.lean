import Mathlib

theorem number_theory_106891 (p : ℕ) (hp : p.Prime) :
    (p^2 + 14).Prime ↔ p = 3 := by 
  constructor
  · -- Assume p^2 + 14 is prime, prove p = 3
    intro h
    by_cases h2 : p > 3
    · -- p > 3
      have h3 : p % 3 = 1 ∨ p % 3 = 2 := by 
        by_contra h4
        push_neg at h4
        have h5 : p % 3 = 0 := by 
          omega
        have h6 : p ≠ 3 := by 
          omega
        have h7 : 3 ∣ p := by 
          omega
        have h8 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
        contradiction
      have h4 : (p ^ 2 + 14) % 3 = 0 := by
        rcases h3 with (h3 | h3)
        · -- p % 3 = 1
          simp [Nat.pow_mod, Nat.add_mod, h3]
          all_goals 
            omega
        · -- p % 3 = 2
          simp [Nat.pow_mod, Nat.add_mod, h3]
          all_goals 
            omega
      have h5 : ¬(p ^ 2 + 14).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 14) by omega) (by nlinarith [h2, show p ≥ 4 by omega]) (by nlinarith [h2, show p ≥ 4 by omega])
      contradiction 
    · -- p ≤ 3
      interval_cases p <;> norm_num at hp h ⊢ <;> tauto
  · -- Assume p = 3, prove p^2 + 14 is prime
    intro h
    rw [show p = 3 by linarith [h]]
    norm_num