import Mathlib

theorem algebra_205995 (x : ℝ) (hx : x ≠ 0) (h1 : (1 / 2) * x + 1 = (1 / 2) * ((1 / 2) * x + 1) + 2)
    (h2 : (1 / 2) * ((1 / 2) * x + 1) + 2 = (1 / 2) * ((1 / 2) * ((1 / 2) * x + 1) + 2) + 1) :
    x = 18 := by
  linarith