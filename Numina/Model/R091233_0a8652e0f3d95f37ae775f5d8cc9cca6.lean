import Mathlib

theorem algebra_197347 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : 1 * v1 + 24 / 60 * v2 = 70) (h2 : 1 * v2 + 24 / 60 * v1 = 70 - 2 * v1)
    (h3 : 1 * v1 + 24 / 60 * v2 + 20 / 60 * v1 = 70 - 2 * v2) :
    v1 = 35 := by
  linarith