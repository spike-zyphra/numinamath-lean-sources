import Mathlib

theorem inequalities_3190 (x y : ℤ) (h1 : (2 * x - 1) / 4 > x + 3) (h2 : (y + 5) / 4 - (2 - y) / 6 ≥ 1) :
    x - y ≤ -8 := by 
  omega