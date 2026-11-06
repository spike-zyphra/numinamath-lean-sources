import Mathlib

theorem algebra_8071
    {a b : ℝ}
    (h : a * 2 ^ 3 + 2 ^ 2 + b * 2 + 327 = 2011) :
    a * (-2) ^ 3 + (-2) ^ 2 + b * (-2) + 327 = -1349 := by
  linarith