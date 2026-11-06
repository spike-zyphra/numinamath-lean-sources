import Mathlib

theorem number_theory_287524 (a b c : ℕ) (ha : a = 32) (hb : b = 24)
    (hc : c * 5 = b * 4 + a * 8) (hd : c * 6 = b * 5 + a * 9) :
    c = 17 := by
  subst ha
  subst hb
  omega