import Mathlib

theorem number_theory_128178 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a * 3^3 + b * 4^3 + c * 5^3 = 577) (h1 : a + b + c = 10) :
    a = 5 := by 
  omega