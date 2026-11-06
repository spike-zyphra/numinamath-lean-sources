import Mathlib

theorem algebra_283623 (a b c d e : ℕ) (ha : a = 7) (hb : b = 7) (hc : c = 7)
    (hd : d = 14) (he : e = 15) : (a + b + c + d + e) / 5 = 10 := by
  subst ha hb hc hd he
  norm_num