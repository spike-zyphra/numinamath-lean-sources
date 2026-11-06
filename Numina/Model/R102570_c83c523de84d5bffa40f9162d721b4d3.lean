import Mathlib

theorem algebra_183489 (a : ℕ) (ha : a > 0) (h : ∃ d, d > 0 ∧ a + 2 * d ≤ 7 ∧ a + 4 * d = 30) :
    a = 5 ∨ a = 6 ∨ a = 7 := by
  rcases h with ⟨d, hd, h1, h2⟩
  omega