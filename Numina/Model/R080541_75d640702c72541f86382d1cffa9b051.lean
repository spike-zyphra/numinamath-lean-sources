import Mathlib

theorem algebra_6900 (n : ℤ) : ∃ m, n * (n + 1) * (n + 2) * (n + 3) + 1 = m ^ 2 := by
  use n ^ 2 + 3 * n + 1
  ring