import Mathlib

theorem algebra_176429 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 4 * a + 3 * b = 1000 / 5) (h2 : 2 * a + 2 * b = 180 / 2) :
    a + b = 65 := by 
  linarith