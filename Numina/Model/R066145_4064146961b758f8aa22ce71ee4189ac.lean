import Mathlib

theorem algebra_3589 : ∑ r in Finset.Icc 1 326, r * (326 - r + 1) = 5827576 := by
  native_decide