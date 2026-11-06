import Mathlib

theorem number_theory_98100 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h1 : a < 100) (h2 : b < 100) (h3 : c < 100) (h4 : a + b = 19) (h5 : b + c = 23)
    (h6 : a + c = 25) :
    c = 11 := by 
  omega