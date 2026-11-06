import Mathlib

theorem algebra_1218 (d c s : ℝ) (hd : d > 0) (hc : c > 0) (hs : s > 0)
(h1 : d = c + 10) (h2 : d = s + 18) (h3 : c * 400 = d * 600) :
c * 1570 = d * 1000 := by 
  rw [h1] at h3
  nlinarith