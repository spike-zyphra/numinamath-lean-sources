import Mathlib

open Real

theorem algebra_21474 (tall earthradius : ℝ) (h1 : tall = 5) : (2 * π * (earthradius + tall) - 2 * π * earthradius)  = 10 * π := by 
  rw [h1]
  ring