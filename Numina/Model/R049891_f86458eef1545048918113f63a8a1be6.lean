import Mathlib

theorem number_theory_108486 {a b c : ℕ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a % 2 = 1) (h2 : b % 2 = 1) (h3 : c % 2 = 1)
    (h4 : a * 12 = b * 21) (h5 : b * 13 = c * 18) :
    b * 12 = c * 7 := by
  omega