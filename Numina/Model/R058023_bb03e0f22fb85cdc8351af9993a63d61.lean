import Mathlib

theorem algebra_96431 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 100 = b * 60) (h2 : a * 240 = b * 180) :
    2 * π * a = 480 := by 
  nlinarith