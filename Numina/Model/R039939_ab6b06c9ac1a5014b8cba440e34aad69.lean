import Mathlib

theorem algebra_135066 : (∑ i in Finset.Icc 1 2016, i) = 2033136 ∧ (∑ i in Finset.Icc 1 2016, (2017 - i)) = 2033136 := by 
  constructor
  · -- Show that the sum from 1 to 2016 is 2033136
    native_decide
  · -- Show that the reversed sum from 1 to 2016 is also 2033136
    native_decide