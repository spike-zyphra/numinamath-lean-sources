import Mathlib

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_96438 : ∑ i in Finset.Icc 1 10000, sumOfDigits i = 180001 := by 
  native_decide