import Mathlib

theorem number_theory_288360 {n : ℕ} (h₀ : n ≥ 100) (h₁ : n ≤ 9999) :
    ∃ a b, a + b = n + (n / 100) ∧ a - b = 171 ∨ a - b = 1513 := by
  use 1514, 1
  right
  all_goals omega