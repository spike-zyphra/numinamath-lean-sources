import Mathlib

theorem algebra_245790 (x y z : ℝ) :
    (x + y + z)^2 = ((1 / 2) * ((x - y)^2 + (y - z)^2 + (z - x)^2) +
      3 * (x * y + y * z + z * x)) := by 
  ring