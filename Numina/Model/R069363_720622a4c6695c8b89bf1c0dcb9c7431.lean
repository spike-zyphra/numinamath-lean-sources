import Mathlib

theorem number_theory_292522 (a b : ℕ) (h : ∃ k, a % 1000 = k ∧ b % 1000 = k) :
    ∃ m, a^3 ≡ m [MOD 1000] ∧ b^3 ≡ m [MOD 1000] := by
  rcases h with ⟨k, h_a, h_b⟩
  use k^3
  constructor
  · -- Show that a^3 ≡ k^3 [MOD 1000]
    simp [Nat.ModEq] at *
    have h1 : a % 1000 = k := h_a
    have h2 : a^3 % 1000 = k^3 % 1000 := by
      have : a % 1000 = k := h1
      norm_num [Nat.pow_mod, this]
    omega
  · -- Show that b^3 ≡ k^3 [MOD 1000]
    simp [Nat.ModEq] at *
    have h1 : b % 1000 = k := h_b
    have h2 : b^3 % 1000 = k^3 % 1000 := by
      have : b % 1000 = k := h1
      norm_num [Nat.pow_mod, this]
    omega