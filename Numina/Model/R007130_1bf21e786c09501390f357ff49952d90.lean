import Mathlib

theorem algebra_610798 :
    ∑ i in Finset.Icc 1 (99 : ℕ), (∑ j in Finset.Icc (i + 1) 100, j : ℚ) / (∑ j in Finset.Icc 1 i, j : ℚ) = 9900 := by 
  native_decide