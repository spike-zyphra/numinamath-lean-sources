import Mathlib

theorem algebra_14297 {x y a b : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h1 : 6 * x - 4 * y = a) (h2 : 6 * y - 9 * x = b)
    (hb : b ≠ 0) : a / b = -2 / 3 := by
  have eq3 : 3 * a + 2 * b = 0 := by
    linarith [h1, h2]
  have eq4 : a = -2 / 3 * b := by
    linarith [eq3]
  field_simp [hb]
  linarith [eq4]