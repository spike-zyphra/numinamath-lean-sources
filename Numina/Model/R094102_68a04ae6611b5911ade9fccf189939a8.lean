import Mathlib

theorem number_theory_314439 (p : ℕ) (hp : p > 0 ∧ Odd p) : p^2 ≡ 1 [MOD 8] := by
  have h1 : p > 0 := hp.1
  have h2 : Odd p := hp.2
  have h : p % 2 = 1 := by
    rcases h2 with ⟨k, hk⟩
    omega
  have h3 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    omega
  rcases h3 with (h | h | h | h)
  · -- Case p % 8 = 1
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case p % 8 = 3
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case p % 8 = 5
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case p % 8 = 7
    simp [Nat.ModEq, Nat.pow_mod, h]