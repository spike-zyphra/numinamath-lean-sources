import Mathlib

theorem algebra_176778 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 10 = b * 11) (h2 : a * 720 = b * 720 - 10 * 60) :
    a = 1 / 80 := by
  nlinarith