import Mathlib

theorem algebra_256564 (d t : ℝ) (ht : t > 0) (h1 : d / 100 = t - 8) (h2 : d / 300 = t - 2)
    (h3 : d / 900 = t - x) :
    x = 12 := by
  linarith