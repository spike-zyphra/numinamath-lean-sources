import Mathlib

theorem algebra_195789 (x y z : ℝ) :
    (x^2 + y^2) * (y^2 + z^2) = (x * y + y * z)^2 ↔ y ^ 2 = x * z := by
  constructor
  · -- Forward direction: If (x^2 + y^2) * (y^2 + z^2) = (x * y + y * z)^2, then y^2 = x * z.
    intro h
    nlinarith [sq_nonneg (y ^ 2 - x * z), sq_nonneg (y * (z - x)), sq_nonneg (x * z - y ^ 2), sq_nonneg (x - z)]
  · -- Backward direction: If y^2 = x * z, then (x^2 + y^2) * (y^2 + z^2) = (x * y + y * z)^2.
    intro h
    nlinarith [sq_nonneg (y ^ 2 - x * z), sq_nonneg (y * (z - x)), sq_nonneg (x * z - y ^ 2), sq_nonneg (x - z)]