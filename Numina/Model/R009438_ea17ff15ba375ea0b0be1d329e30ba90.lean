import Mathlib

theorem algebra_11646 : ∑ x in (Finset.Ioo 300 500).filter Odd, x = 40000 := by 
  native_decide