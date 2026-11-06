import Mathlib

theorem number_theory_184414 (p : ℕ) (hp : p.Prime) :
    (p + 50).Prime ∧ (p - 50).Prime ↔ p = 53 := by
  constructor
  · -- Assume that both p + 50 and p - 50 are prime, prove that p = 53
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p > 53
    · -- p > 53
      have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      rcases h4 with (h4 | h4 | h4)
      · -- p % 3 = 0
        have h5 : p % 3 = 0 := by
          omega
        have h6 : p > 3 := by
          omega
        have h7 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p % 3 = 1
        have h8 : (p + 50) % 3 = 0 := by
          omega
        have h9 : p + 50 > 3 := by
          omega
        have h10 : ¬(p + 50).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 50) by omega)
          all_goals omega
        contradiction
      · -- p % 3 = 2
        have h10 : (p - 50) % 3 = 0 := by
          omega
        have h11 : p - 50 > 3 := by
          omega
        have h12 : ¬(p - 50).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p - 50) by omega)
          all_goals omega
        contradiction
    · -- p ≤ 53
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto
  · -- Assume p = 53, prove that both p + 50 and p - 50 are prime
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num