import Mathlib

theorem algebra_291575 (x a b : ℝ) :
    (x + a) * (x + b) ∣ (x + a + b)^3 - x^3 - a^3 - b^3 := by
  use 3 * (a + b)
  ring_nf