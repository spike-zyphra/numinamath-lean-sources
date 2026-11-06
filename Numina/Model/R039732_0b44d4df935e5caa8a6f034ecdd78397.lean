import Mathlib

theorem algebra_270796 (a d : ℤ) :
    ∃ x y, a^2 + 2 * (a + d)^2 + 3 * (a + 2 * d)^2 + 4 * (a + 3 * d)^2 = x^2 + y^2 := by 
  use (3 * a + 5 * d), (a + 5 * d)
  ring_nf