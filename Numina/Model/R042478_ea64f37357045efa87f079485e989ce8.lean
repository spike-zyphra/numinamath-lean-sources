import Mathlib

theorem number_theory_175509 (r : ℚ) :
    ∃ w x y z : ℚ, r = w^3 + x^3 + y^3 + z^3 := by
  use (r / 6 + 1)
  use (r / 6 - 1)
  use (-r / 6)
  use (-r / 6)
  ring_nf