import Mathlib

/- A floor 9 feet by 12 feet, is to be tiled with 4-inch-by-6-inch tiles. How many tiles are needed to cover the floor? -/
theorem algebra_13293 :
    ((9 * 12) * (12 * 12)) / (4 * 6 : ℝ) = 648 := by
  norm_num
