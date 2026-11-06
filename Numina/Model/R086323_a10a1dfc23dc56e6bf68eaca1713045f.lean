import Mathlib

theorem number_theory_69055 : (∑ k in Finset.Icc 0 62, Nat.choose 2014 k) % 2017 = 1024 := by 
  native_decide