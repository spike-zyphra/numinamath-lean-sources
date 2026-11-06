import Mathlib

theorem algebra_292174 {x y z a b c : ℤ} (h1 : x + y - z = a - b) (h2 : x - y + z = b - c)
    (h3 : -x + y + z = c - a) : x + y + z = 0 := by 
  linarith