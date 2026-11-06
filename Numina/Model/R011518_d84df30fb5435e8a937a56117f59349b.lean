import Mathlib

theorem number_theory_257019: (Nat.divisors (2^9*3^14)).card = 150 := by
  have h3 : Nat.Coprime (2^9) (3^14) := by
    norm_num [Nat.Coprime]
  have h4 : (Nat.divisors (2^9 * 3^14)).card = (Nat.divisors (2^9)).card * (Nat.divisors (3^14)).card := by 
    rw [Nat.Coprime.card_divisors_mul]
    exact h3
  have h5 : (Nat.divisors (2^9)).card = 10 := by
    rw [Nat.divisors_prime_pow]
    all_goals norm_num
  have h6 : (Nat.divisors (3^14)).card = 15 := by 
    rw [Nat.divisors_prime_pow]
    all_goals norm_num
  calc 
    (Nat.divisors (2^9 * 3^14)).card = (Nat.divisors (2^9)).card * (Nat.divisors (3^14)).card := h4
    _ = 10 * 15 := by rw [h5, h6]
    _ = 150 := by norm_num