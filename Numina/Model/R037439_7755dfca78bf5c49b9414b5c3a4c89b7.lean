import Mathlib

theorem number_theory_93499 :
    ∃ m k : ℕ, m > 0 ∧ k > 0 ∧ (m * 6 ^ k).divisors.card = 2021 ∧ ¬(6 ∣ m) ∧ m + k = 58 := by 
  use 16, 42
  constructor
  · -- $m > 0$
    norm_num
  constructor
  · -- $k > 0$
    norm_num
  constructor
  · -- Show that the number of divisors of $16 \cdot 6^{42}$ is 2021
    have h1 : (16 * 6 ^ 42 : ℕ) = 2 ^ 46 * 3 ^ 42 := by
      norm_num
    rw [h1]
    have h2 : ((2 ^ 46 * 3 ^ 42 : ℕ)).divisors.card = (46 + 1) * (42 + 1) := by 
      have h5 : (2 ^ 46 * 3 ^ 42).divisors.card = (2 ^ 46).divisors.card * (3 ^ 42).divisors.card := by
        rw [Nat.Coprime.card_divisors_mul]
        all_goals norm_num
      rw [h5]
      have h6 : (2 ^ 46 : ℕ).divisors.card = 46 + 1 := by
        rw [Nat.divisors_prime_pow (by norm_num)]
        simp [Finset.card_range]
        all_goals try { norm_num }
      have h7 : (3 ^ 42 : ℕ).divisors.card = 42 + 1 := by
        rw [Nat.divisors_prime_pow (by norm_num)]
        simp [Finset.card_range]
        all_goals try { norm_num }
      rw [h6, h7]
      all_goals try { norm_num }
    rw [h2]
    all_goals norm_num
  constructor
  · -- $6 \nmid m$
    norm_num
  · -- $m + k = 58$
    norm_num