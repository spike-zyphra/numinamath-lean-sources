import Mathlib

theorem algebra_18841 (total : ℝ) (h : total ≠ 0) (h1 : (80 / 100) * total = 48) :
    (20 / 100) * total = 12 := by 
  have ht : total = 60 := by
    linarith
  rw [ht]
  norm_num