import Mathlib

theorem number_theory_2751 {a b c d : ℤ} : ∃ x y, (a^2 + a * b + b^2) * (c^2 + c * d + d^2) = x^2 + x * y + y^2 := by
  use (a * c - b * d)
  use (a * d + b * c + b * d)
  ring