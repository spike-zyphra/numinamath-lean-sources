import Mathlib

theorem number_theory_186691 :
    (∑ i in Finset.Icc 1 2013, if Odd i then (Nat.digits 10 i).sum else 0) -
    (∑ i in Finset.Icc 1 2012, if Even i then (Nat.digits 10 i).sum else 0) = 1007 := by 
  native_decide