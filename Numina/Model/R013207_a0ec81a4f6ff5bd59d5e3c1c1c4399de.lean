import Mathlib

open Real

theorem inequalities_6823 {x y : ℝ} (h : (x + 3) ^ 2 ≤ (y + 3) ^ 2) :
    abs (x + 3) ≤ abs (y + 3) := by
  apply sq_le_sq.1
  linarith