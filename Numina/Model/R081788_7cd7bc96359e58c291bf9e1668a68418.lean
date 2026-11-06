import Mathlib

theorem algebra_217063 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 12 = b * 36) (h2 : a * 1620 = b * 12) :
    b * 1620 = a * 36 := by 
  nlinarith