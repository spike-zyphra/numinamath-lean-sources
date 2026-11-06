import Mathlib

theorem number_theory_218974 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a + b + c = 961 + 1001) (h1 : a + b = 961) (h2 : b + c = 1001) :
    a + c = 154 := by 
  omega