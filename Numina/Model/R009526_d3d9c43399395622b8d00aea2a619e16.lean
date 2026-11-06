import Mathlib

theorem algebra_95796 (x : ℝ) (h : x ≠ 0) (h1 : (60 + 100 + x + 40 + 50 + 200 + 90) / 7 = x)
(h2 : (60 + 100 + x + 40 + 50 + 200 + 90) / 7 = (x + 40) / 2) (h3 : (60 + 100 + x + 40 + 50 + 200 + 90) / 7 = x) :
x = 90 := by
  linarith