import Mathlib

theorem algebra_22200 (x y z : ℝ) (h1 : 4 * x - y + 2 * z = 7) (h2 : 6 * x + 3 * y + 3 * z = 5) :
    y = -11 / 9 := by 
  have eq1 : 12 * x - 3 * y + 6 * z = 21 := by
    linarith [h1]

  have eq2 : 12 * x + 6 * y + 6 * z = 10 := by
    linarith [h2]

  have eq3 : 9 * y = -11 := by
    linarith [eq1, eq2]

  have eq4 : y = -11 / 9 := by
    linarith

  linarith [eq4]