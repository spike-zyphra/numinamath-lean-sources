import Mathlib

theorem algebra_163464 (x : ℝ) (hx : x > 100) (h1 : (x - 20 / 100) * 3 = (x + 20 / 100) * 4) :
    x = 198 := by 
  linarith