import Mathlib

theorem algebra_21197 : ∑ i ∈ Finset.Icc (2 : ℕ) 100, (1 / ((i : ℚ)^3 - i)) = 5049 / 20200 := by 
  native_decide