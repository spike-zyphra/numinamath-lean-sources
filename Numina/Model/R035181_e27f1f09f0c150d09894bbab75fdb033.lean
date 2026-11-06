import Mathlib

theorem algebra_288353 (x y : ℝ) :
    (x + y) ^ 3 - x ^ 3 - y ^ 3 = 3 * x * y * (x + y) ∧
    (x + y) ^ 5 - x ^ 5 - y ^ 5 = 5 * x * y * (x + y) * (x ^ 2 + x * y + y ^ 2) ∧
    (x + y) ^ 7 - x ^ 7 - y ^ 7 = 7 * x * y * (x + y) * (x ^ 2 + x * y + y ^ 2) ^ 2 := by
  constructor
  · -- Prove the first identity
    ring
  constructor
  · -- Prove the second identity
    ring
  · -- Prove the third identity
    ring