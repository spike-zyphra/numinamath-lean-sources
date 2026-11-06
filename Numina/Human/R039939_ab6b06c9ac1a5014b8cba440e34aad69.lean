import Mathlib

theorem algebra_135066 : (∑ i in Finset.Icc 1 2016, i) = 2033136 ∧ (∑ i in Finset.Icc 1 2016, (2017 - i)) = 2033136 := by
  native_decide