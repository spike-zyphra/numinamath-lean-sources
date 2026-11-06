import Mathlib

theorem number_theory_110984 (a b c d e : ℕ) (ha : a < b) (hb : b < c) (hc : c < d)
    (hd : d < e) (h1 : a + b = 10) (h2 : d + e = 18) :
    a + b + c + d + e = 35 := by
  have h3 : c = 7 := by
    omega
  linarith [h1, h2, h3]