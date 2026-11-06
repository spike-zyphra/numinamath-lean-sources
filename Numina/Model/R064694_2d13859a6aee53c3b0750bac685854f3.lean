import Mathlib

theorem algebra_2444 : (∏ i ∈ Finset.Icc (1 : ℕ) 9, (1 + (7 : ℚ) / i)) / (∏ i ∈ Finset.Icc (1 : ℕ) 7, (1 + (9 : ℚ) / i)) = 1 := by 
  native_decide