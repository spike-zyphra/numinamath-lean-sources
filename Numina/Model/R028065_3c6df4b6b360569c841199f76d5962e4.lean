import Mathlib

theorem algebra_176227 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 2 * x + 5 * y = 0.5) (h2 : 5 * x + 8 * y = 0.95) :
    1 / x = 12 := by
  have eq1 : 2 * x + 5 * y = (1 / 2 : ℝ) := by
    rw [h1]
    norm_num
  have eq2 : 5 * x + 8 * y = (19 / 20 : ℝ) := by
    rw [h2]
    norm_num
  have eq3 : x = (1 / 12 : ℝ) := by
    linarith [eq1, eq2]
  have hx' : 1 / x = 12 := by
    rw [eq3]
    field_simp
  exact hx'