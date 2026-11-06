import Mathlib

theorem number_theory_198490 : ∑ n in Finset.Icc 1 2017, (Nat.digits 10 n).count 7 = 602 := by
  native_decide