import Mathlib

open Real

/- If a girl 5 feet tall could walk around the equator, how many feet further would the top of her head travel than her feet? Assume that the earth is a sphere. Express your answer in terms of $\pi$. -/
theorem algebra_21474 (tall earthradius : ℝ) (h1 : tall = 5) : (2 * π * (earthradius + tall) - 2 * π * earthradius)  = 10 * π := by
  rw [h1]
  ring
