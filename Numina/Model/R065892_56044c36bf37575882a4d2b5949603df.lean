import Mathlib

theorem algebra_173204 {x y : ℤ} (h : x * y + 900 = (x - 3) * (y + 3)) :
    x * y - 918 = (x + 3) * (y - 3) := by 
  nlinarith