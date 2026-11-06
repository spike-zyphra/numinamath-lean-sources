import Mathlib

theorem algebra_3666 (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (h1 : x * a = x * b + 80) (h2 : x * a = x * c + 100) (h3 : x * b = x * c + 25) :
    x = 400 := by
  nlinarith