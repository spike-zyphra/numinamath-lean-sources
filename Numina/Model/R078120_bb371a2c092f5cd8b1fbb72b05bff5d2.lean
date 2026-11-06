import Mathlib

theorem algebra_122123 (father daughter : ℕ) (h₁ : father - 7 = 5 * (daughter - 7)) (h₂ : father = 3 * daughter) :
    ∃ x, father + x = 2 * (daughter + x) := by
  use (father - 2 * daughter)
  omega