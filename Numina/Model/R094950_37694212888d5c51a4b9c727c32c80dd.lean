import Mathlib

theorem algebra_216894 (d : ℝ) (h : d > 0) (h1 : (10 / 60) * d = (d - (10 / 60) * d) / 2)
    (h2 : (10 / 60) * d = 2015) : d = 2418 := by
  linarith