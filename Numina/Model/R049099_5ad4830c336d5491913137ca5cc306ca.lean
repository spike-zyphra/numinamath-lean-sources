import Mathlib

theorem number_theory_96348 : (Nat.digits 10 (∑ i ∈ Finset.Icc 7 2006, Nat.factorial i)).length > 1 ∧
    (Nat.digits 10 (∑ i ∈ Finset.Icc 7 2006, Nat.factorial i))[1]! = 4 := by 
  native_decide