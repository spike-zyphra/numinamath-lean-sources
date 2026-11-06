import Mathlib

/- A rectangular box has a volume of 108 cubic feet. How many cubic yards are in the volume of this box? -/
theorem algebra_10559 (x y z : ℝ) (h : x * y * z = 108) :
    (x / 3) * (y / 3) * (z / 3) = 4 := by 
  field_simp
  linarith