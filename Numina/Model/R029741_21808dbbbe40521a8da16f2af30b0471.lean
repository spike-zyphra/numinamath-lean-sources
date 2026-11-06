import Mathlib

theorem number_theory_316799 (p : ℕ) (hp : Nat.Prime p) (h : p > 5)
    (h1 : p ≡ 1 [MOD 4]) :
    ∀ a : ℤ, ∃ b c : ℤ, a = b + c ∧ ¬∃ x : ℤ, x^2 ≡ b [ZMOD p] ∧
      ¬∃ x : ℤ, x^2 ≡ c [ZMOD p] := by
  intro a
  use a, 0
  constructor
  · -- Show that a = a + 0
    ring
  · -- Show that ¬∃ x, x^2 ≡ a [ZMOD p] ∧ ¬∃ x, x^2 ≡ 0 [ZMOD p]
    intro h
    rcases h with ⟨x, hx, h2⟩
    have h3 : ∃ x : ℤ, x^2 ≡ (0 : ℤ) [ZMOD p] := by
      use (0 : ℤ)
      simp [Int.ModEq]
    have h4 := h2 h3
    all_goals contradiction