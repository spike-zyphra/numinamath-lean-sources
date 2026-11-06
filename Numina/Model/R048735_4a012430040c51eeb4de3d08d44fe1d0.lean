import Mathlib

theorem algebra_292456 {a b : ℝ} :
    (a - b) * (a + b) * (a^2 + a * b + b^2) * (a^2 - a * b + b^2) =
    a^6 - b^6 := by
  ring