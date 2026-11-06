import Mathlib

theorem number_theory_277473 : (Nat.digits 10 709).length = 3 ∧
    ∑ i ∈ Finset.Icc 1 709, (Nat.digits 10 i).length = 2019 := by
  constructor
  · -- Show that (Nat.digits 10 709).length = 3
    norm_num
  · -- Show that ∑ i ∈ Finset.Icc 1 709, (Nat.digits 10 i).length = 2019
    native_decide