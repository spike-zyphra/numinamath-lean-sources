import Mathlib

theorem number_theory_191377 (p : ℕ) (hp : p.Prime) :
    (2 * p ^ 2 + 1).Prime ↔ p = 3 := by
  constructor
  · -- Assume $2 * p ^ 2 + 1$ is prime, prove $p = 3$.
    intro h
    by_cases h3 : p ≤ 3
    · -- Case where p ≤ 3. Since p is prime, possible values are 2 and 3.
      interval_cases p <;> norm_num at hp h ⊢ <;> try tauto
    · -- Case where p > 3.
      push_neg at h3
      have h1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
          omega
      rcases h1 with (h | h | h)
      · -- Case where p % 3 = 0
        have h4 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by
            omega
          ) (by omega) (by omega)
        contradiction
      · -- Case where p % 3 = 1
        have h5 : (2 * p ^ 2 + 1) % 3 = 0 := by
          have h1' : p % 3 = 1 := h
          have h2 : p ^ 2 % 3 = 1 := by
            simp [Nat.pow_mod, h1']
          omega
        have h6 : ¬ (2 * p ^ 2 + 1).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ 2 * p ^ 2 + 1 by 
            omega
          ) (by nlinarith [show p > 0 from by linarith, h3]) (by nlinarith [show p > 0 from by linarith, h3])
        contradiction
      · -- Case where p % 3 = 2
        have h5 : (2 * p ^ 2 + 1) % 3 = 0 := by
          have h2' : p % 3 = 2 := h
          have h2 : p ^ 2 % 3 = 1 := by
            simp [Nat.pow_mod, h2']
          omega
        have h6 : ¬ (2 * p ^ 2 + 1).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ 2 * p ^ 2 + 1 by 
            omega
          ) (by nlinarith [show p > 0 from by linarith, h3]) (by nlinarith [show p > 0 from by linarith, h3])
        contradiction
  · -- Assume p = 3, prove (2 * p ^ 2 + 1) is prime.
    intro h
    rw [h]
    norm_num