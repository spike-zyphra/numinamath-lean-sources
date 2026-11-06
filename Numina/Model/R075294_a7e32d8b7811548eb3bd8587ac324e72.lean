import Mathlib

theorem algebra_214210 (n : ℝ) (hn : n = 0.125) :
    (n * 106) / 132.5 = 10 / 100 := by 
  rw [hn]
  norm_num