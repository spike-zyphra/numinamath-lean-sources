import Mathlib

theorem algebra_20893 (x y z : ℝ) (h : x + y + z = 77) (h1 : x / 4 = y / 2) (h2 : y / 2 = z) :
    x = 44 := by
  have eq1 : x = 2 * y := by
    linarith
  have eq2 : y = 2 * z := by
    linarith
  have eq3 : x = 4 * z := by
    linarith [eq1, eq2]
  have eq4 : 7 * z = 77 := by
    linarith [h, eq3, eq2]
  have eq5 : z = 11 := by
    linarith
  rw [eq5] at eq3
  linarith