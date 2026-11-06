import Mathlib

theorem algebra_47003 (n : ℤ) : IsSquare ((n * (n + 1) * (n + 2) * (n + 3) + 1)) := by
  use n ^ 2 + 3 * n + 1
  ring