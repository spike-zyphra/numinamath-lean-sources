import Mathlib

theorem algebra_208721 (x : ℝ) (hx : x > 0) (h1 : (x / 2 + 3) + (x - (x / 2 + 3)) / 2 + 3 = x - 18) :
    x = 90 := by
  linarith