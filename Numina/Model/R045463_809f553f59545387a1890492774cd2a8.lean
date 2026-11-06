import Mathlib

theorem algebra_199827 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a * 4 + b * 1 + c * 2 + d * 5 = 10) (h2 : a * 2 + b * 3 + c * 2 + d * 1 = 7)
    (h3 : a * 5 + b * 2 + c * 1 + d * 4 = 14) :
    a * 4 + b * 4 + c * 4 + d * 4 = 12 := by
  linarith