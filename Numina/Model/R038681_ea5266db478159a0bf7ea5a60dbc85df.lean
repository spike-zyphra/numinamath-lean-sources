import Mathlib
open Real

theorem algebra_1403 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
(h1 : (x - 1) / 2 = (2 - y) / 3) (h2 : (2 - y) / 3 = (z - 3) / 4) :
19 ≤ 3 * x + 4 * y + 5 * z ∧ 3 * x + 4 * y + 5 * z ≤ 35 + 1 / 3 := by
  constructor
  · -- Prove 19 ≤ 3 * x + 4 * y + 5 * z (minimum)
    linarith
  · -- Prove 3 * x + 4 * y + 5 * z ≤ 35 + 1 / 3 (maximum)
    linarith