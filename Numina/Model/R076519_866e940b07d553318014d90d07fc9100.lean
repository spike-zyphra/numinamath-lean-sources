import Mathlib

theorem algebra_314645 : (∑ k in Finset.Icc 1 2015, k * 2 ^ k) % 100 = 6 := by
  native_decide