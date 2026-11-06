import Mathlib

theorem number_theory_118917 (a b c d : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hd : d > 0) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : 1989 < a) (h5 : 1989 < b)
    (h6 : 1989 < c) (h7 : 1989 < d) (h8 : (a + b) / 2 = 1997) (h9 : (c + d) / 2 = 2004)
    (h10 : (a + c) / 2 = 2009) (h11 : (b + d) / 2 = 2012) :
    a = 1997 ∧ b = 2004 ∧ c = 2009 ∧ d = 2012 := by 
  omega