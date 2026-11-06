import Mathlib

theorem number_theory_8186 : ∃ n : ℕ, 5^1000 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 0 := by 
  use 0
  constructor
  · -- Show that 5^1000 divides 0
    exact dvd_zero (5 ^ 1000)
  · -- Show that 0 has no zero digits
    intro d hd
    simpa using hd