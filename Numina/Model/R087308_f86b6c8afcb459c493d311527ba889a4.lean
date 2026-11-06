import Mathlib

theorem algebra_21641 : ∑ x in (Finset.Ioo 10 20).filter (fun y => ¬Nat.Prime y), x = 75 := by
  native_decide