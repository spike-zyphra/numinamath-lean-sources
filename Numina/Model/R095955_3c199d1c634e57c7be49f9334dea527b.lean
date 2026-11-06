import Mathlib

theorem algebra_15262 {a b c s : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hs : s > 0) (h : a^2 = b^2 + c^2) (h1 : c = 5 / 2) (h2 : b = Real.sqrt 3 / 2 * 5)
    (h3 : s = 8) :
    (s / 2 - (-s / 2)) / (c - (-c)) = 8 / 5 := by 
  rw [h3]
  rw [h1]
  norm_num