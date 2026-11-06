import Mathlib

theorem number_theory_196509 (p : ℕ) (hp : p.Prime) :
    (p + 10).Prime ∧ (p + 14).Prime ↔ p = 3 := by
  constructor
  · -- Assume (p + 10).Prime ∧ (p + 14).Prime, prove p = 3
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p ≤ 3
    · -- Assume p ≤ 3
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto
    · -- Assume p > 3
      push_neg at h3
      have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases h4 with (h4 | h4 | h4)
      · -- Case p % 3 = 0
        have h5 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
        contradiction
      · -- Case p % 3 = 1
        have h6 : (p + 14) % 3 = 0 := by
          omega
        have h7 : ¬ (p + 14).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 14) by omega) (by omega) (by omega)
        contradiction
      · -- Case p % 3 = 2
        have h8 : (p + 10) % 3 = 0 := by
          omega
        have h9 : ¬ (p + 10).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 10) by omega) (by omega) (by omega)
        contradiction
  · -- Backward implication: Assume p = 3, prove (p + 10).Prime ∧ (p + 14).Prime
    intro h
    rw [h]
    constructor
    · -- Show 13 is prime
      norm_num
    · -- Show 17 is prime
      norm_num