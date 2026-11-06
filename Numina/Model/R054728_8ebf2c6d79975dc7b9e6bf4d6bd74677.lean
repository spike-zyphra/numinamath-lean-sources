import Mathlib

def f (n : ℕ) : ℕ := (∑ i in Finset.Icc 1 n, i) % 10

theorem number_theory_13744 : ∑ i in Finset.Icc 1 2011, f i = 7046 := by 
  native_decide