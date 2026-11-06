import Mathlib

theorem algebra_240685 {x : ℝ} (hx : x > 0) (h1 : 38 * x = 1) (h2 : 8 * 5 * x = 1) :
    1 / x = 75 := by
  exfalso 
  nlinarith