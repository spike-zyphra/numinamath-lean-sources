import Mathlib

theorem number_theory_237389 (n : ℕ) :
    (Nat.Prime (3 * n - 4)) ∧ (Nat.Prime (4 * n - 5)) ∧ (Nat.Prime (5 * n - 3)) ↔ n = 2 := by
  constructor
  · -- Assume Nat.Prime (3 * n - 4)) ∧ (Nat.Prime (4 * n - 5)) ∧ (Nat.Prime (5 * n - 3)), prove n = 2
    intro h
    rcases h with ⟨h1, h2, h3⟩
    by_cases h4 : n > 2
    · -- n > 2
      by_cases h5 : n % 2 = 0
      · -- n is even
        have h6 : (3 * n - 4) % 2 = 0 := by
          omega
        -- contradiction: 3n - 4 is even and >= 2 is not prime
        have h8 : n ≥ 3 := by omega
        have h9 : 3 * n - 4 ≥ 2 := by omega
        have h10 : ¬ Nat.Prime (3 * n - 4) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (3 * n - 4) by omega)
          all_goals omega
        contradiction
      · -- n is odd
        have h7 : n % 2 = 1 := by
          omega
        have h8 : (5 * n - 3) % 2 = 0 := by
          omega
        -- contradiction: 5n - 3 is even and >= 2 is not prime
        have h9 : n ≥ 3 := by omega
        have h10 : 5 * n - 3 ≥ 2 := by omega
        have h11 : ¬ Nat.Prime (5 * n - 3) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (5 * n - 3) by omega)
          all_goals omega
        contradiction
    · -- n ≤ 2
      have h5 : n ≤ 2 := by linarith
      interval_cases n <;> norm_num at h1 h2 h3 ⊢ <;> try tauto
  · -- Assume n = 2, prove Nat.Prime (3 * n - 4)) ∧ (Nat.Prime (4 * n - 5)) ∧ (Nat.Prime (5 * n - 3))
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num