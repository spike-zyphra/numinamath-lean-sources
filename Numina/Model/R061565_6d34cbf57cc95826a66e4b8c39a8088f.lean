import Mathlib

theorem number_theory_182015 :
    (∑ n in Finset.Icc 1 1000, n.divisors.sum id) < 1000000 := by
  native_decide