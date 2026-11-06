import Mathlib

theorem number_theory_318770 (p : ℕ) (h₀ : Odd p) : p^2 ≡ 1 [MOD 8] := by
  have h1 : p % 2 = 1 := by
    rcases h₀ with ⟨k, hk⟩
    omega
  have h2 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    omega
  rcases h2 with (h | h | h | h)
  · -- case $p \equiv 1 \pmod 8$
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- case $p \equiv 3 \pmod 8$
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- case $p \equiv 5 \pmod 8$
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- case $p \equiv 7 \pmod 8$
    simp [Nat.ModEq, Nat.pow_mod, h]