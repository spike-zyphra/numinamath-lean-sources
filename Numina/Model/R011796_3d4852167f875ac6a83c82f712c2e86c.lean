import Mathlib

theorem algebra_288581 {a b c : ℝ} :
    (x - a)^2 * (b - c) + (x - b)^2 * (c - a) + (x - c)^2 * (a - b) = -(a-b)*(b-c)*(c-a) := by
  ring