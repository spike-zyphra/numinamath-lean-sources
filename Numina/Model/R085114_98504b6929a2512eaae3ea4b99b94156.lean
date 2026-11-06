import Mathlib

theorem number_theory_1212 (x : ℕ) (h0 : x % 3 = 2)
  (h1 : x % 4 = 3) (h2 : x % 5 = 4) :
  x % 15 = 14 := by 
  omega