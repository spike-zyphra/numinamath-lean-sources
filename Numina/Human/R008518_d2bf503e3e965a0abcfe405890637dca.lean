import Mathlib

/- In 2003, the average monthly rainfall in Mathborough was $41.5\text{ mm.}$ In 2004, the average monthly rainfall in Mathborough was $2\text{ mm}$ more than in 2003. What was the total amount of rain that fell in Mathborough in 2004? -/
theorem algebra_15627 (r : ℝ) (h : r = 41.5 + 2) :
    12 * r = 522 := by
  rw [h]
  ring