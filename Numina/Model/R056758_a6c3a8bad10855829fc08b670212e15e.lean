import Mathlib

def a (n : ℕ) := (10 ^ n - 1) * 10 ^ 3 + 744

def f (n : ℕ) := Nat.factorization (a n) 2

theorem number_theory_88847 : ∑ i in Finset.Icc 1 10, f i = 75 := by 
  native_decide