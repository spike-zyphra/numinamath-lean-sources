import Mathlib

theorem number_theory_155737 : ∑ k in Finset.Icc 1 2009, k * ((2009 / k) - (2008 / k)) = 2394 := by 
  native_decide