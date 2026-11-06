import Mathlib

theorem algebra_177004 {x y z : ℝ} (h : x + y + z = 24) (h1 : x - y - z = y + z)
    (h2 : y - x - z = x + z) (h3 : z - x - y = x + y) :
    x = 13 ∧ y = 7 ∧ z = 4 := by 
  exfalso 
  linarith