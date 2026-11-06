import Mathlib

theorem number_theory_247803 : (∑ n in Finset.Icc 1 2015, n * 10 ^ (n - 1)) % 9 = 0 := by 
  native_decide