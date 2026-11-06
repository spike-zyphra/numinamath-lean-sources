import Mathlib

theorem algebra_152992 (a b c d : ℝ) :
    (a - b) * (b + c + d) * (c + a + d) + (b - c) * (c + a + d) * (a + b + d) + (c - a) * (a + b + d) * (b + c + d) = (b - c) * (a - b) * (a - c) := by
  ring