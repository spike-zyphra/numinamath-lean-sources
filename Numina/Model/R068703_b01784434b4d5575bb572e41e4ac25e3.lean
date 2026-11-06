import Mathlib

theorem algebra_774 (a b c : ℝ) : (b - c) ^ 5 + (c - a) ^ 5 + (a - b) ^ 5 =
    5 * (a - b) * (b - c) * (c - a) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
  ring