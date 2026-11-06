import Mathlib

theorem algebra_18759 : (Nat.factorial 42) % 10^9 = 0 ∧ (Nat.factorial 42) % 10^10 ≠ 0 := by
  constructor
  · -- First part: showing 42! % 10^9 = 0
    native_decide
  · -- Second part: showing 42! % 10^10 ≠ 0
    native_decide