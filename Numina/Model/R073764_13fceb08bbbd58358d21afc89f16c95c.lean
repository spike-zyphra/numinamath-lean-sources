import Mathlib

theorem algebra_226979 (a b c d : ℤ) (hb : b > 0) (h1 : a + b = c) (h2 : b + c = d)
    (h3 : c + d = a) :
    a + b + c + d ≤ -5 := by 
  omega