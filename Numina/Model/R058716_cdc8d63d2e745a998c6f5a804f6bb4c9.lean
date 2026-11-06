import Mathlib

theorem algebra_33770 : ∃ x y z : ℤ, x - 3 * y + 2 * z = 1 ∧ 2 * x + y - 5 * z = 7 ∧ z = 4 ^ 111 := by
  use 1 + 3 * ((5 + 9 * (4 ^ 111)) / 7) - 2 * (4 ^ 111),
    (5 + 9 * (4 ^ 111)) / 7, 4 ^ 111
  constructor
  · -- Verify the first equation: x - 3y + 2z = 1
    norm_num
    <;> omega
  constructor
  · -- Verify the second equation: 2x + y - 5z = 7
    norm_num
    <;> omega
  · -- Verify that z = 4 ^ 111
    rfl