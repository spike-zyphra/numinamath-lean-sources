import Mathlib

theorem number_theory_206960 : ∃ n, 5^1000 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 0 := by
  use 0
  constructor
  · -- Show that 5^1000 divides 0
    simp
  · -- Show that all digits of 0 (there are none) are not zero
    simp