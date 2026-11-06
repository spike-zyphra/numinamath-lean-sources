import Mathlib

theorem algebra_149688 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : b = a + c) (h2 : b = a + 25) (h3 : c = b + 25) :
    c - a = 3 := by 
  linarith