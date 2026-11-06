import Mathlib

theorem algebra_297651 (a b c d : ℤ) :
    ∃ m n, (a^2 + b^2) * (c^2 + d^2) = m^2 + n^2 := by
  use a * c - b * d, a * d + b * c
  ring