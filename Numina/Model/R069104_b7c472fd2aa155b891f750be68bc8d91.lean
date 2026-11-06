import Mathlib

theorem number_theory_56576 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (p ^ 2 + 2) ↔ p = 3 := by 
  constructor
  · -- Assume h : Nat.Prime (p ^ 2 + 2), want p = 3
    intro h
    by_cases h1 : p ≤ 3
    · -- p ≤ 3
      interval_cases p <;> norm_num at hp h ⊢ <;> trivial
    · -- p > 3
      push_neg at h1
      have h2 : p % 3 = 1 ∨ p % 3 = 2 := by 
        by_contra h3
        push_neg at h3
        have h4 : p % 3 = 0 := by omega
        have h5 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      rcases h2 with (h2 | h2)
      · -- p ≡ 1 (mod 3)
        have h3 : (p ^ 2) % 3 = 1 := by
          norm_num [Nat.pow_mod, h2]
        have h4 : (p ^ 2 + 2) % 3 = 0 := by
          omega
        have h5 : ¬Nat.Prime (p ^ 2 + 2) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p ^ 2 + 2 by omega)
          all_goals
            nlinarith
        contradiction
      · -- p ≡ 2 (mod 3)
        have h3 : (p ^ 2) % 3 = 1 := by
          norm_num [Nat.pow_mod, h2]
        have h4 : (p ^ 2 + 2) % 3 = 0 := by
          omega
        have h5 : ¬Nat.Prime (p ^ 2 + 2) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p ^ 2 + 2 by omega)
          all_goals
            nlinarith
        contradiction
  · -- Assume p = 3, prove Nat.Prime (p ^ 2 + 2)
    intro hp_eq
    rw [hp_eq]
    norm_num