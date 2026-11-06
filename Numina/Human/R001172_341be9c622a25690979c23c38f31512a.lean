import Mathlib

/- Estimate $14.7923412^2$ to the nearest hundred. -/
theorem algebra_20848 : round (14.7923412^2 / 100 : ℚ) * 100 = 200 := by norm_num [round_eq]
