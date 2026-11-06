import Mathlib

theorem algebra_130655 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c = (a + b) / 3) (hd : d = 2 * (a + b) / 3)
    (h1 : 0 < c) (h2 : 0 < d) (h3 : c < d) (h4 : a * 12 = b * 8 + c * 4)
    (h5 : a * 30 = b * 16 + c * 12) :
    d = 16 := by
  nlinarith [h4, h5, hc, hd, h3, ha, hb]