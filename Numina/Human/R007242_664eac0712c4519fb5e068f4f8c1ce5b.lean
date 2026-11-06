import Mathlib

/- When a water tank is $30\%$ full, it contains 27 gallons less than when it is $20\%$ empty. How many gallons of water does the tank hold when it is full? -/
theorem algebra_13900 {x : ℝ} (hx : x ≠ 0)
    (h1 : (30 / 100) * x = (1 - 20 / 100) * x - 27) :
    x = 54 := by
  linarith