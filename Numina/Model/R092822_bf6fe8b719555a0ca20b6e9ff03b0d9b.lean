import Mathlib

theorem algebra_143999 (a x b : ℝ) (h : x ≠ 0) (h1 : a ≠ 0) (h2 : b ≠ 0)
    (h3 : a + x = b) (h4 : a + 2 * x = 2 * b) :
    a / b = 1 / 3 := by
  have h5 : a = 0 := by
    linarith [h3, h4]
  contradiction