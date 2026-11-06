import Mathlib

theorem number_theory_106662 (p : ℕ) (hp : p.Prime) :
    (p + 4).Prime ∧ (p + 8).Prime ↔ p = 3 := by
  constructor
  · -- Assume (p + 4).Prime ∧ (p + 8).Prime, prove p = 3
    rintro ⟨h1, h2⟩
    by_cases h3 : p ≤ 5
    · interval_cases p <;> norm_num at hp h1 h2 <;> try { trivial }
    · -- p > 5
      have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      rcases h4 with (h | h | h)
      · -- p % 3 = 0
        have h5 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p % 3 = 1
        have h6 : (p + 8) % 3 = 0 := by
          omega
        have h5 : ¬ (p + 8).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 8) by omega)
          all_goals omega
        contradiction
      · -- p % 3 = 2
        have h7 : (p + 4) % 3 = 0 := by
          omega
        have h5 : ¬ (p + 4).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by omega)
          all_goals omega
        contradiction
  · -- Assume p = 3, prove (p + 4).Prime ∧ (p + 8).Prime
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num