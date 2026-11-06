import Mathlib

theorem number_theory_189624 {a b c : ℕ} (h₀ : 0 ≤ b ∧ b ≤ 6) (h₁ : 49 * a + 7 * b + c = 121 * c + 11 * b + a) :
    (b = 6 ∧ 2 * a - 5 * c = 1) ∨ (b = 0 ∧ 2 * a - 5 * c = 0) := by
  omega