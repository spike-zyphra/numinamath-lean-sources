import Mathlib

theorem number_theory_4479 {n : ℕ} (hn : 1 < n) : ∃ p, p.Prime ∧ p ∣ n := by
  have h2 : n ≠ 1 := by linarith
  apply Nat.exists_prime_and_dvd
  all_goals linarith