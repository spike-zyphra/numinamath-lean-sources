import Mathlib

theorem algebra_3789 {a b c : ℝ} :
  (a - b) ^ 3 + (b - c) ^ 3 - (a - c) ^ 3 = 3 * (a - c) * (a - b) * (c - b) := by
  ring