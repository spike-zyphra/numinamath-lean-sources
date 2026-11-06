import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_309106 (x y z w : ℝ) (hx : x ≥ y) (hy : y ≥ z) (hz : z ≥ w) (hw : w ≥ 0)
  (h : 5 * x + 4 * y + 3 * z + 6 * w = 100) :
  x + y + z + w ≤ 45 ∧ x + y + z + w ≥ 5 := by
  constructor
  · -- Show that x + y + z + w ≤ 45
    linarith [h, hx, hy, hz, hw]
  · -- Show that x + y + z + w ≥ 5
    linarith [h, hx, hy, hz, hw]