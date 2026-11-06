import Mathlib

open Nat

theorem number_theory_3780 : (∑ i in Finset.Icc 1 2023, i !) % 100 = 13 := by
  native_decide