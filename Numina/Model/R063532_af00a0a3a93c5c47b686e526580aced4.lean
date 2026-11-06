import Mathlib

theorem algebra_175168 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (hxy : x + y = 10) (h : x = 3 * y) (h' : y ≠ 0) :
    x = 7.5 := by
  have eq1 : x + y = 10 := hxy
  have eq2 : x = 3 * y := h
  have eq3 : y = 10 / 4 := by
    linarith [eq1, eq2]
  have eq4 : x = 30 / 4 := by
    rw [eq3] at eq2
    linarith [eq2]
  rw [eq4]
  norm_num