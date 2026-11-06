import Mathlib

theorem number_theory_226948 {n : ℕ} (hn : n > 3) :
    ∃ k, k > 0 ∧ (n - k) % 2 = 0 ∧ ¬(n - k) % 4 = 0 := by
  use n - 2
  constructor
  · -- Show that k = n - 2 > 0 since n > 3.
    omega
  constructor
  · -- Show that (n - (n - 2)) % 2 = 0
    omega
  · -- Show that ¬(n - (n - 2)) % 4 = 0
    omega