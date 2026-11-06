import Mathlib

/- The diagonal lengths of a rhombus are 24 units and 10 units. What is the area of the rhombus, in square units? -/
theorem algebra_11252 {a b c d : ℝ} (ha : a = 24) (hb : b = 10) :
    (1/2) * a * b = 120 := by
  rw [ha, hb]
  ring