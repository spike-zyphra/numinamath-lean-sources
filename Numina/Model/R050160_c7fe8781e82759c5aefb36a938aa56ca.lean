import Mathlib

theorem algebra_284287 (x y z a b c : ℝ) :
    (a * x + b * y + c * z) ^ 2 +
    (b * x + c * y + a * z) ^ 2 +
    (c * x + a * y + b * z) ^ 2 =
    (c * x + b * y + a * z) ^ 2 +
    (b * x + a * y + c * z) ^ 2 +
    (a * x + c * y + b * z) ^ 2 := by
  ring