import Mathlib

open Real

theorem algebra_319074 : (∏ i ∈ Finset.Icc 2 100, (i ^ 3 - 1)) / (∏ i ∈ Finset.Icc 2 100, (i ^ 3 + 1)) = 2 / 3 := by 
  native_decide