import Mathlib

theorem number_theory_7738 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h1 : x * 2 + y * 3 = 43) (h2 : x * 3 + y * 2 = 61) :
    x + y = 20 := by 
  omega