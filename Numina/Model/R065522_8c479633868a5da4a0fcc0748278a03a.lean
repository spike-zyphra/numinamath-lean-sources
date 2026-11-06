import Mathlib

theorem number_theory_8420 :
    ∀ n : ℕ, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n := by
  intro n hn
  have h : n ≠ 1 := by linarith
  apply Nat.exists_prime_and_dvd
  exact h