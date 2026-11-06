import Mathlib

theorem algebra_284427 {x y : ℝ} (h : x + y = 1500) (h1 : 3 * x = 4 * y) (h2 : x = 690) (h3 : y = 1080) :
    x = 600 ∧ y = 900 := by 
  exfalso
  linarith