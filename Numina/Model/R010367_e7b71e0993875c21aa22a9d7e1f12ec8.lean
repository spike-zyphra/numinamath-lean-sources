import Mathlib

open ArithmeticFunction

theorem number_theory_13310 : ((Finset.Icc 1 25).filter fun n => (σ 1 n).Prime).card = 5 := by 
  native_decide