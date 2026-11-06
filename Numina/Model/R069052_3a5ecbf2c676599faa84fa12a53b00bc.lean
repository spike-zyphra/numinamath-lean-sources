import Mathlib

def petrovSum : ℕ := ∑ n in Finset.Icc 1 2013, if Odd n then (Nat.digits 10 n).sum else 0

def vasechkinSum : ℕ := ∑ n in Finset.Icc 2 2012, if Even n then (Nat.digits 10 n).sum else 0

theorem number_theory_187782 : petrovSum - vasechkinSum = 1007 := by
  native_decide