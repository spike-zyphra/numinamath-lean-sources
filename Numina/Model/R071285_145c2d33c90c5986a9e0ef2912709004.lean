import Mathlib

theorem number_theory_131146 (a b c : ℕ) (ha : 1 ≤ a ∧ a ≤ 8) (h : 10000 * a + 1000 * b + 100 * c + 10 * b + a = 10000 * (a + 1) + 1000 * 9 + 100 * 9 + 10 * 9 + (a + 1)) :
    a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 := by
  rcases ha with ⟨ha1, ha2⟩
  omega