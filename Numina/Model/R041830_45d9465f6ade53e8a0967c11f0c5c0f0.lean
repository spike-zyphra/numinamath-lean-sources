import Mathlib

theorem number_theory_202233 (p : ℕ) (hp : Nat.Prime p) (h : p > 5)
    (h1 : p ≡ 1 [MOD 4]) (a : ℤ) :
    ∃ b c : ℤ, a = b + c ∧ ¬∃ x : ℤ, x^2 ≡ b [ZMOD p] ∧
    ¬∃ x : ℤ, x^2 ≡ c [ZMOD p] := by
  use a, 0
  constructor
  · -- Show that a = a + 0
    ring
  · -- Show that it is false that there exists x such that x^2 ≡ a and ¬∃ x : x^2 ≡ 0
    intro h
    rcases h with ⟨x, hx, h'⟩
    have h0 : ∃ y, y^2 ≡ (0 : ℤ) [ZMOD p] := ⟨0, by
      simp [Int.ModEq]⟩
    have h' : ¬∃ y : ℤ, y^2 ≡ (0 : ℤ) [ZMOD p] := by 
      simpa using h' 
    contradiction