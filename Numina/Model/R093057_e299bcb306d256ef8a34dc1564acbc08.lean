import Mathlib

theorem algebra_1342 (l t d : ℝ) (hl : l > 0) (ht : t > 0) (h : d > 0)
    (h1 : 60 * (1 - 2 / 5) = t * (2 / 5) + d) (h2 : 60 * 2 / 5 = t * (3 / 5) + d) :
    t = 12 := by
  linarith