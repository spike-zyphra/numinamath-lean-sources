import Mathlib

theorem algebra_135659 (a b : ℤ) :
    ∃ x y z t : ℤ,
      x + y + 2 * z + 2 * t = a ∧
      2 * x - 2 * y + z - t = b := by 

  use -2 * a + 4 * b
  use -a + 2 * b
  use 2 * a - 3 * b
  use 0
  constructor
  · -- Verify the first equation
    ring
  · -- Verify the second equation
    ring