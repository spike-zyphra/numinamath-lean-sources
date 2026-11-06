import Mathlib

theorem algebra_14129 (milk : ℝ) (h : milk = 3) (james : ℝ) (hj : james = 12 / 5) :
    milk - james = 3 / 5 := by 
  rw [h, hj]
  norm_num -- Lean can compute 3 - 12/5 to get 3/5