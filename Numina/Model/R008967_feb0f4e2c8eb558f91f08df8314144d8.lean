import Mathlib

theorem algebra_10398 : ∑ i in (Finset.Icc 11 39).filter Odd, i = 375 := by 
  native_decide