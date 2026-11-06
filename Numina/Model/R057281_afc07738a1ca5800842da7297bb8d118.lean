import Mathlib

theorem number_theory_184281 (a b c d e : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10)
    (hd : d < 10) (he : e < 10) (h : (130000 + 10000 * a + 1000 * b + 100 * c + 10 * d + e) / 5 =
    100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + 6) :
    1326530 / 5 = 265306 := by 
  norm_num