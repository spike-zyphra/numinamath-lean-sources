import Mathlib

theorem number_theory_14472 : (∑ k in Finset.range 63, Nat.choose 2014 k) % 2017 = 1024 := by
  native_decide