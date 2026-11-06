import Mathlib

theorem number_theory_6358 (p d1 d2 : ℕ) (hp : Nat.Prime p) (hd1 : ¬p ∣ d1) (hd2 : ¬p ∣ d2)
    (h : p > 2) :
    ((∃ x, x^2 ≡ d1 [MOD p]) ∧ (∃ y, y^2 ≡ d2 [MOD p])) →
    ∃ z, z^2 ≡ d1 * d2 [MOD p] := by
  intro h1
  rcases h1.1 with ⟨x, hx⟩
  rcases h1.2 with ⟨y, hy⟩
  use x * y
  have hxy1 : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
    ring
  rw [hxy1]
  have hxy2 : x ^ 2 * y ^ 2 ≡ d1 * d2 [MOD p] := by
    have h2 : x ^ 2 ≡ d1 [MOD p] := hx
    have h3 : y ^ 2 ≡ d2 [MOD p] := hy
    exact Nat.ModEq.mul h2 h3
  exact hxy2