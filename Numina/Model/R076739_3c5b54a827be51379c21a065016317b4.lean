import Mathlib

theorem algebra_12944 (S : Finset ℕ) (hS : S = {2, 4}) :
    (S.card : ℝ) / 6 = 1 / 3 := by 
  rw [hS]
  norm_num