import Mathlib

theorem number_theory_278776 : ∃ k, k^2 = Nat.factorial 20 * Nat.factorial 19 / 5 := by
  use 2 * Nat.factorial 19
  native_decide