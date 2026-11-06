import Mathlib

theorem algebra_1225 (s b c t : ℝ) (hs : s > 0) (hb : b > 0) (hc : c > 0) (h1 : b * 10 = c * 5) (h2 : b * 15 = c * 10 + t * 5) (ht : t > 0) : t = 15 := by
  nlinarith