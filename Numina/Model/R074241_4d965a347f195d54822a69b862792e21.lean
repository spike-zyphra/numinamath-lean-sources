import Mathlib

theorem algebra_235411 (s i : ℝ) (hs : s > 0) (hi : i > 0)
    (h1 : s * 10 = i * 5) (h2 : s * 600 = i * 300 + 5 * 300) :
    i = 15 := by 
  nlinarith