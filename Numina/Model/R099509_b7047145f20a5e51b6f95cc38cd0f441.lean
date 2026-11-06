import Mathlib

theorem algebra_281575 (a b c d : ℤ) (ha : a = 1) (hb : b = 10) (hc : c = 100) (hd : d = 1000) :
    (a + b + c - d) + (a + b - c + d) + (a - b + c + d) + (-a + b + c + d) = 2222 := by 
  rw [ha, hb, hc, hd]
  norm_num