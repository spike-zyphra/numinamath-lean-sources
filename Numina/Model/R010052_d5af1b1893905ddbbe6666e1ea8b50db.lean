import Mathlib
open Real
theorem number_theory_95293 :
(Nat.minFac 55 = 5 ∧ Nat.minFac 57 = 3 ∧ Nat.minFac 58 = 2 ∧ Nat.minFac 59 = 59 ∧ Nat.minFac 61 = 61) := by
  constructor
  · -- Show Nat.minFac 55 = 5
    native_decide

  constructor
  · -- Show Nat.minFac 57 = 3
    native_decide

  constructor
  · -- Show Nat.minFac 58 = 2
    native_decide

  constructor
  · -- Show Nat.minFac 59 = 59
    native_decide

  · -- Show Nat.minFac 61 = 61
    native_decide