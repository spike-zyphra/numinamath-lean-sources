import Mathlib

theorem number_theory_127171 (x : ℝ) (hx : x = 80 + 19 / 100) :
    ∃ n m, x = (1 + 10 / 100) ^ n * (1 - 10 / 100) ^ m * 100 := by 
  use 1, 3
  rw [hx]
  norm_num