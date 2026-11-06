import Mathlib

theorem number_theory_608884 (n : ℕ) (hn : n > 2) : Even (Nat.totient n) := by
  have h1 : n ≥ 3 := by linarith
  apply Nat.totient_even
  all_goals linarith