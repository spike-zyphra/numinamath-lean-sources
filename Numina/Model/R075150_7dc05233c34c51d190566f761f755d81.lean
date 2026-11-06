import Mathlib

theorem algebra_176719 (y j b : ℝ)
    (hy : y = 4 * j + 6 * (j + b) + 9 * j)
    (hj : j ≠ 0)
    (hb : b ≠ 0)
    (h1 : y = (1 / 3) * j)
    (h2 : b = 2 * y) :
    j = 30 ∧ y = 24 ∧ b = 18 := by
  have eq1 : y = 19 * j + 6 * b := by
    linarith [hy]
  rw [h2] at eq1
  have eq2 : y = -19 / 11 * j := by
    nlinarith
  have h3 : j = 0 := by
    linarith [h1, eq2]
  contradiction