import Mathlib

theorem algebra_2625 {x y : ℝ} (h1 : 3 * x + y = 7) (h2 : 5 * x - 8 * y = 31) :
    x = 3 ∧ y = -2 := by 
  constructor 
  · -- Solving the equations to get x = 3
    linarith 
  · -- Solving the equations to get y = -2
    linarith