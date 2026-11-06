import Mathlib

theorem algebra_101913 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 10 * 8 = x + y * 8) (h2 : 15 + 14 + 13 + 12 + 11 = x + y * 5) : y = 5 := by
  have eq1 : 80 = x + y * 8 := by
    linarith
  have eq2 : (15 + 14 + 13 + 12 + 11 : ℝ) = x + y * 5 := by
    linarith
  have eq3 : (65 : ℝ) = x + y * 5 := by
    norm_num at eq2 ⊢
    linarith
  have eq4 : y = 5 := by
    linarith [eq1, eq3]
  linarith [eq4]