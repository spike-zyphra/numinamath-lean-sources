import Mathlib

theorem algebra_135732 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 6 + b * 6 = 144) (h2 : a * 6 + (b + 5) * 6 = 12) (h3 : (a + 5) * 6 + b * 6 = 16) :
    a = 30 := by
  linarith