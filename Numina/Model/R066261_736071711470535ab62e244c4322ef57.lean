import Mathlib

theorem number_theory_254900 (m n : ℤ) : ∃ a b, (2*m^2 + n^2)^2 = 2*a^2 + b^2 := by
  use (0 : ℤ)
  use (2 * m^2 + n^2 : ℤ)
  ring_nf