import Mathlib


theorem number_theory_244743 : ∑ n in Finset.Icc 1 2011, (Nat.digits 10 n).sum = 28072 := by native_decide