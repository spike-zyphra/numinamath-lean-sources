import Mathlib

set_option exponentiation.threshold 2009
set_option maxRecDepth 10000

theorem number_theory_15394 : (∑ i in Finset.Icc 1 2009, i^2009) % 10 = 5 := by 
  native_decide