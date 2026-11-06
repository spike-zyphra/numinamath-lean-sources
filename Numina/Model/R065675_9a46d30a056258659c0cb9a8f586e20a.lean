import Mathlib

theorem algebra_125861 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * 1 = b * 4) (h' : b * 15 = a * 86 + b * 4) :
    a * 15 = b * 86 := by 
  nlinarith