import Mathlib

theorem algebra_114297 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : x ^ 2 * 100 + y * 3 = 5000000) (h' : (x / 2) ^ 2 * 100 + y / 2 * 3 = 2000000) :
    x ^ 2 * 100 = 2000000 := by
  have eq1 : 25 * x ^ 2 + (3 / 2) * y = 2000000 := by 
    nlinarith
  have eq2 : x ^ 2 * 100 + 3 * y = 5000000 := by
    linarith
  have eq3 : 50 * x ^ 2 + 3 * y = 4000000 := by
    linarith [eq1]
  have eq4 : x ^ 2 * 50 = 1000000 := by
    nlinarith [eq2, eq3]
  linarith [eq4]