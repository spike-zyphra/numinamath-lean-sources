import Mathlib

theorem algebra_15531 {a b c d e f : ℝ}
    (ha : a = 0) (hb : b = Real.sqrt 3) (hc : c = Real.sqrt 3 + 2)
    (hd : d = 2) (he : e = 0) (hf : f = 2) :
    48 / 4 = 72 / 6 := by 
  norm_num