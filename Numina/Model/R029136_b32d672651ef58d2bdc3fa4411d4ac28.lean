import Mathlib

theorem algebra_12493 : (Nat.card ((Finset.Icc 1 3) × (Finset.Icc 4 7))) = 12 := by
  simp [Finset.Icc]
  native_decide