import Mathlib

theorem algebra_198361 {x0 y0 : ℝ} (hx : x0 ≠ 0) (hy : y0 ≠ 0)
    (h1 : x0 / 3 + y0 / 5 = 1) (h2 : x0 / 5 + y0 / 3 = 1) :
    1 / x0 + 1 / y0 = 16 / 15 := by
  have eq1 : 5 * x0 + 3 * y0 = 15 := by
    linarith [h1]
  have eq2 : 3 * x0 + 5 * y0 = 15 := by
    linarith [h2]
  have h_eq3 : x0 + y0 = 15 / 4 := by
    linarith [eq1, eq2]
  have h_eq4 : x0 = y0 := by
    linarith [eq1, eq2]
  have h_x0 : x0 = 15 / 8 := by
    linarith [h_eq3, h_eq4]
  have h_y0 : y0 = 15 / 8 := by
    linarith [h_eq3, h_eq4]
  rw [h_x0, h_y0]
  norm_num