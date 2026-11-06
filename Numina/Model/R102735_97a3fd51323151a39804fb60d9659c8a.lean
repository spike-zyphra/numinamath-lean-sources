import Mathlib

theorem number_theory_153491 : ∃ n : ℕ, 2^100 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 0 := by
  use 0
  constructor
  · -- Show that 2^100 divides 0
    exact dvd_zero _
  · -- Show that for all digits d in Nat.digits 10 0, d ≠ 0
    intro d hd
    simpa using hd