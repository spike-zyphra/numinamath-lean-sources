import Mathlib

theorem number_theory_221143 : ∑ x in (Finset.Icc 1 100).filter Odd, x = 2500 := by 
  native_decide