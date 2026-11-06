import Mathlib

theorem algebra_95654 {N : ℕ} (hN : N = 69^5 + 5 * 69^4 + 10 * 69^3 + 10 * 69^2 + 5 * 69 + 1) :
    (Nat.divisors N).card = 216 := by
  have h11 : N = 70^5 := by 
    norm_num [hN]
  rw [h11]
  rw [show (70 ^ 5 : ℕ) = 2^5 * 5^5 * 7^5 by norm_num]
  have h2 : (Nat.divisors (2^5 * 5^5 * 7^5 : ℕ)).card = 216 := by
    have h3 : (2^5 * 5^5 * 7^5 : ℕ) ≠ 0 := by
      norm_num 
    rw [Nat.card_divisors (show (2^5 * 5^5 * 7^5 : ℕ) ≠ 0 by exact h3)]
    rw [Nat.factorization]
    native_decide 
  exact h2