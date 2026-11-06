import Mathlib

theorem algebra_278557 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2)
    (h3 : 40 = v1 * 14 + v2 * 11) (h4 : 30 = v1 * 46 + v2 * 30)
    (h5 : 30 = v1 * 10 + v2 * 7) :
    |v1 - v2| = 37.5 := by
  linarith