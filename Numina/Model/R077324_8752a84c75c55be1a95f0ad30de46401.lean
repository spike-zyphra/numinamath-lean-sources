import Mathlib

theorem algebra_99932 (x y z : ℝ) (h1 : 3 * x + 4 * y - 2 * z = 5) (h2 : 2 * x + 3 * y - z = 3) :
    (x - 3) / 2 = (y + 1) / (-1) ∧ (y + 1) / (-1) = z / 1 := by
  constructor
  · -- First part: show (x - 3) / 2 = (y + 1) / (-1)
    field_simp
    linarith [h1, h2]
  · -- Second part: show (y + 1) / (-1) = z / 1
    field_simp
    linarith [h1, h2]