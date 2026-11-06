import Mathlib

theorem number_theory_629554 (n:ℕ) (hn: n=2022^2022):
n.divisors.card = 2023^3 := by 
  rw [hn]
  have h1 : (2022 ^ 2022 : ℕ) = (2 ^ 2022 * 3 ^ 2022 * 337 ^ 2022 : ℕ) := by
    have h2 : (2022 : ℕ) = (2 * 3 * 337 : ℕ) := by 
      norm_num
    calc 
      (2022 ^ 2022 : ℕ) = ((2 * 3 * 337 : ℕ) ) ^ 2022 := by 
        rw [show (2022 : ℕ) = (2 * 3 * 337 : ℕ) by exact h2]
      _ = (2 * 3 * 337) ^ 2022 := by 
        all_goals norm_num
      _ = (2 ^ 2022 * 3 ^ 2022 * 337 ^ 2022 : ℕ) := by 
        ring_nf
  rw [h1]

  have h3 : Nat.Coprime (2 ^ 2022 * 3 ^ 2022) (337 ^ 2022) := by
    have h4 : Nat.Coprime (2 ^ 2022 * 3 ^ 2022) 337 := by
      have h2 : Nat.Coprime (2 ^ 2022) 337 := by
        norm_num
      have h3 : Nat.Coprime (3 ^ 2022) 337 := by
        norm_num
      have h4 : Nat.Coprime (2 ^ 2022 * 3 ^ 2022) 337 := by
        apply Nat.Coprime.mul
        exact h2
        exact h3
      exact h4
    have h5 : Nat.Coprime (2 ^ 2022 * 3 ^ 2022) (337 ^ 2022) := by
      apply Nat.Coprime.pow_right
      exact h4
    exact h5

  have h6 : ((2 ^ 2022 * 3 ^ 2022 * 337 ^ 2022)).divisors.card =
          (2 ^ 2022 * 3 ^ 2022).divisors.card * (337 ^ 2022).divisors.card := by
    rw [Nat.Coprime.card_divisors_mul]
    exact h3

  have h7 : (2 ^ 2022 * 3 ^ 2022).divisors.card =
          (2 ^ 2022).divisors.card * (3 ^ 2022).divisors.card := by
    have h8 : Nat.Coprime (2 ^ 2022) (3 ^ 2022) := by
      norm_num
    rw [Nat.Coprime.card_divisors_mul]
    exact h8

  have h8 : (2 ^ 2022).divisors.card = 2023 := by
    rw [Nat.divisors_prime_pow]
    all_goals 
      norm_num

  have h9 : (3 ^ 2022).divisors.card = 2023 := by
    rw [Nat.divisors_prime_pow]
    all_goals 
      norm_num

  have h10 : (337 ^ 2022).divisors.card = 2023 := by
    rw [Nat.divisors_prime_pow]
    all_goals 
      norm_num

  rw [h6, h7, h8, h9, h10]
  all_goals 
    norm_num