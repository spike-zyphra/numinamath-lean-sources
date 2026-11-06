import Mathlib

theorem algebra_1580
    {a : ℝ}
    (ha : a < 0) :
    |a - (-a)| = -2 * a := by
  have h1 : a - (-a) = 2 * a := by ring
  rw [h1]
  have h2 : 2 * a < 0 := by linarith
  rw [abs_of_neg h2]
  ring