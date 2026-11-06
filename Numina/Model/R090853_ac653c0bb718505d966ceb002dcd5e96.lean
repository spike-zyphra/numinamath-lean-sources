import Mathlib

theorem algebra_26895 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * 29 = b * 19) (h2 : b * 11 = a * 19 + b * 10) :
    a * 12 = 179 := by 
  nlinarith