import Mathlib

theorem algebra_16739 : ((Finset.Icc 10 99).filter fun n => IsSquare (Nat.digits 10 n).sum).card = 17 := by
  native_decide