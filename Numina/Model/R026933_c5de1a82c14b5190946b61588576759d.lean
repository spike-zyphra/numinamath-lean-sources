import Mathlib

theorem algebra_246288 (a b : ℤ) :
    ∃ x y z t : ℤ, x + y + 2 * z + 2 * t = a ∧ 2 * x - 2 * y + z - t = b := by 
  use -2 * a + 4 * b, -a + 2 * b, 2 * a - 3 * b, 0
  constructor
  · -- Check the first equation
    ring
  · -- Check the second equation
    ring