import Mathlib

theorem algebra_601991 (a b : ℤ) :
    ∃ x y z t : ℤ, x + y + 2 * z + 2 * t = a ∧ 2 * x - 2 * y + z - t = b := by
  use -a + b
  use -2 * a + b
  use 0
  use 2 * a - b
  constructor
  · -- Show that the first equation holds with the chosen values.
    ring
  · -- Show that the second equation holds with the chosen values.
    ring