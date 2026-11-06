import Mathlib

theorem algebra_6633 {a b c : ℝ} (h : 3 * a + b + c = 31 ∧ a + 3 * b + c = 15 ∧ a + b + 3 * c = 9) :
    a - b - c = 9 := by
  rcases h with ⟨h1, h2, h3⟩
  linarith