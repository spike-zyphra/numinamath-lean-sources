import Mathlib

theorem number_theory_157485 : (∑ k in Finset.Icc 1 30303, k ^ k) % 101 = 29 := by
  native_decide