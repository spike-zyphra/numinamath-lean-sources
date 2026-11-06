import Mathlib

open Real
open scoped BigOperators

theorem number_theory_224316 {n : ℕ} :
  (n > 0 → ∃ x : ℚ, x = 1 / (2 * n) ∨ x = 1 / (2 * n - 2)) ∧
  (n = 0 → ∃ x : ℚ, x = 1 / 2) := by
  constructor
  · -- Assume n > 0, we need to show ∃ x : ℚ, x = 1 / (2 * n) ∨ x = 1 / (2 * n - 2)
    intro hn
    use 1 / (2 * n)
    left
    rfl
  · -- Assume n = 0, we need to show ∃ x : ℚ, x = 1 / 2
    intro hn
    use (1 / 2)
    all_goals simp [hn]