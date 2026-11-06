import Mathlib

def d (n : ℕ) := (∑ i in Finset.Icc 1 n, i) % 10

theorem number_theory_53601 : (∑ n in Finset.Icc 1 2017, d n) % 1000 = 69 := by 
  native_decide