import Mathlib

theorem number_theory_9175 : ∑ n in Finset.Icc 1 2014, (Nat.floor (n / 2) + Nat.floor (n / 3) + Nat.floor (n / 6)) = 2027091 := by 
  native_decide