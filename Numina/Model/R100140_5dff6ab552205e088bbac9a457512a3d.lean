import Mathlib

def a (n : ℕ) := (∑ i in Finset.Icc 1 n, i) % 10

def S (n : ℕ) := ∑ i in Finset.Icc 1 n, a i

theorem number_theory_225350 : S 2016 = 7066 := by
  native_decide