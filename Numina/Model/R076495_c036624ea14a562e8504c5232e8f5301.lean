import Mathlib

theorem algebra_149432 (m n : ℤ) :
    ∃ w x y z : ℤ, w + x + 2*y + 2*z = m ∧ 2*w - 2*x + y - z = n := by
  use (-m + n), (-2 * m + n), 0, (2 * m - n)
  constructor
  · -- First equation
    ring
  · -- Second equation
    ring