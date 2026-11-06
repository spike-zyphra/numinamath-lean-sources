import Mathlib

theorem number_theory_257189 (p : ℕ) (hp : p.Prime) :
    (p + 2).Prime ∧ (p + 4).Prime ↔ p = 3 := by
  constructor
  · -- Assume (p + 2).Prime ∧ (p + 4).Prime, prove p = 3
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p ≤ 3
    · -- p ≤ 3
      interval_cases p <;> norm_num at hp h1 h2 <;> tauto
    · -- p > 3
      have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      rcases h4 with (h4 | h4 | h4)
      · -- p % 3 = 0
        have h5 : p > 3 := by
          omega
        have h6 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p % 3 = 1
        have h5 : (p + 2) % 3 = 0 := by
          omega
        have h7 : p + 2 > 3 := by
          omega
        have h8 : ¬(p + 2).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2) by omega)
          all_goals omega
        contradiction
      · -- p % 3 = 2
        have h5 : (p + 4) % 3 = 0 := by
          omega
        have h7 : p + 4 > 3 := by
          omega
        have h8 : ¬(p + 4).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by omega)
          all_goals omega
        contradiction
  · -- Assume p = 3, prove (p + 2).Prime ∧ (p + 4).Prime
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num