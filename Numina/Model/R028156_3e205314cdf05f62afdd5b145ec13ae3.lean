import Mathlib

theorem number_theory_175221 (p : ℕ) (hp : Nat.Prime p) (h : 5 < p) :
    ∃ q : ℕ, Nat.Prime q ∧ q < p ∧ ∃ n : ℕ, 0 < n ∧ p ∣ n^2 - q := by
  use 2
  constructor
  · -- Show that 2 is prime
    norm_num
  constructor
  · -- Show that 2 < p
    linarith
  use 1
  constructor
  · -- Show that 1 > 0
    norm_num
  · -- Show that p divides 1^2 - 2
    have hp2 : p > 2 := by linarith
    have h1 : p ∣ (1 ^ 2 - 2 : ℕ) := by
      norm_num
      all_goals linarith
    simpa using h1