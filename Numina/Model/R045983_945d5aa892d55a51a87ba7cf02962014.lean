import Mathlib

theorem algebra_488 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 1 / a + 5 / b = 1 / 30) (h2 : 1 / a + 6 / b = 1 / 20) :
    1 / a + 15 / b = 1 / 5 := by
  have eq1 : a * b = 30 * b + 150 * a := by
    field_simp at h1 h2
    nlinarith [h1]
  have eq2 : a * b = 20 * b + 120 * a := by
    field_simp at h2
    nlinarith [h2]
  have eq3 : 10 * b + 30 * a = 0 := by
    nlinarith [eq1, eq2]
  have eq4 : 10 * b > 0 := by
    linarith [hb]
  have eq5 : 30 * a > 0 := by
    linarith [ha]
  have eq6 : 10 * b + 30 * a > 0 := by
    linarith [eq4, eq5]
  linarith [eq3, eq6]