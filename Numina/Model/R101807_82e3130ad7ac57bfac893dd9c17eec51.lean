import Mathlib

def a (n : ℕ) := (∑ i in Finset.Icc 1 n, i) % 10

def S (n : ℕ) := ∑ i in Finset.range n, a (i + 1)

theorem number_theory_300344 : S 2016 = 7066 := by
  native_decide