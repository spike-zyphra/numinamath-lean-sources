import Mathlib

theorem algebra_22670 : ((Finset.Ioo 0 1000).filter fun n =>
    0 < n.log2 ∧ 2 ∣ n.log2).card = 340 := by
  native_decide