import Mathlib

theorem number_theory_302556 (p : ℕ) (hp : p.Prime) :
    (p + 10).Prime ∧ (p + 14).Prime ↔ p = 3 := by
  constructor
  · -- Assume (p + 10).Prime ∧ (p + 14).Prime, prove p = 3
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p ≤ 3
    · interval_cases p <;> norm_num at hp h1 h2 <;> try { tauto }
    · -- p > 3
      push_neg at h3
      have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases h4 with (h4 | h4 | h4)
      · -- Case $p \equiv 0 \pmod{3}$:
        have h5 : p % 3 = 0 := by
          omega
        have h6 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by linarith) (by linarith)
        contradiction
      · -- Case $p \equiv 1 \pmod{3}$:
        have h5 : (p + 14) % 3 = 0 := by
          omega
        have h6 : ¬(p + 14).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 14) by omega)
          all_goals linarith
        contradiction
      · -- Case $p \equiv 2 \pmod{3}$:
        have h5 : (p + 10) % 3 = 0 := by
          omega
        have h6 : ¬(p + 10).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 10) by omega)
          all_goals linarith
        contradiction
  · -- Assume p = 3, prove (p + 10).Prime ∧ (p + 14).Prime
    intro h
    rw [h]
    constructor
    · -- Show 13 is prime
      norm_num
    · -- Show 17 is prime
      norm_num