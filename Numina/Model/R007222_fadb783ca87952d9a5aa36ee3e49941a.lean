import Mathlib

theorem number_theory_182271 {n : ℕ} (hn : n > 3) :
    ∃ k, k ∣ (2 ^ (Nat.totient n) - 1) ∧ Nat.Coprime k n := by
  use 1
  constructor
  · -- Show that 1 divides 2^(φ n) - 1
    simp
  · -- Show that Nat.Coprime 1 n
    simp