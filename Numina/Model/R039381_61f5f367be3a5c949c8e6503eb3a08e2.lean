import Mathlib

theorem algebra_280656 (a b c d e : ℝ)
    (ha : a = 105000) (hb : b = 52200) (hc : c = 33345) (hd : d = 9350) (he : e = 70000) :
    a + b + c + d + e = 269895 := by
  rw [ha, hb, hc, hd, he]
  norm_num