import Mathlib
open Real

/- If x < -2, then | 1 - | 1 + x | | equals
(A) 2 + x  (B) -2-x (C) x (D) -x (E) - 2 -/
theorem algebra_97493 (x : ℝ) (hx : x < -2) : abs (1 - abs (1 + x)) = -2 - x := by
-- discuss the signs of the absolute values and solve them one by one
  rw [abs_of_nonpos] <;> (try rw [abs_of_nonpos] <;> try linarith)