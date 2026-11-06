import Mathlib

/- In a recent basketball game, Shenille attempted only three-point shots and two-point shots.  She was successful on $20\%$ of her three-point shots and $30\%$ of her two-point shots.  Shenille attempted $30$ shots.  How many points did she score? -/
theorem algebra_10326 (x y x' y' : ℕ) (h : x + y = 30) (h₁ : x' = (20 / 100 : ℚ) * x) (h₂ : y' = (30 / 100 : ℚ) * y) : x' * 3 + y' * 2 = 18 := by
  qify at *
  linarith
