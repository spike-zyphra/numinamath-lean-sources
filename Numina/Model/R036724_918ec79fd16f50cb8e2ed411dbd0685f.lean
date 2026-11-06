import Mathlib

theorem algebra_21881 {a b : ℝ}
    (h1 : a + b + a + b + a + b = 21) (h2 : b + a + b + a + b + a = 16) :
    b + b = 17 / 8 := by
  have eq1 : 3 * a + 3 * b = 21 := by
    linarith
  have eq2 : 3 * a + 3 * b = 16 := by
    linarith
  linarith