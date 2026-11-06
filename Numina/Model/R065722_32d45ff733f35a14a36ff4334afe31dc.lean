import Mathlib

theorem algebra_14679 (a : ℝ) (ha : a = 10) :
    (a^2 - 4 * (π / 4) * (a / 2)^2) = 100 - 25 * π := by
  rw [ha]
  ring_nf
  <;> ring