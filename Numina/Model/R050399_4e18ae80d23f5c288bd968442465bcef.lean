import Mathlib

theorem algebra_138614 (a b c d e : ℝ)
    (ha : a = 20 * 5 + 80 * 3) (hb : b = 20 * 6 + 80 * 2)
    (hc : c = 20 * 7 + 80 * 1) (hd : d = 20 * 8 + 80 * 0)
    (he : e = 20 * 9 + 80 * 9) :
    d < a ∧ d < b ∧ d < c ∧ d < e := by 
  rw [ha, hb, hc, hd, he]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num