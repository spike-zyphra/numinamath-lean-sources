import Mathlib

theorem algebra_241001 (k j : ℝ) (hk : 0 < k) (hj : 0 < j)
    (h1 : k * 8 = j * 3) (h2 : k * 12 = j * 10) :
    j = 288 := by 
  nlinarith [h1, h2, mul_pos hk hj]