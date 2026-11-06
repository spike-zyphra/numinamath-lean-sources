import Mathlib

theorem algebra_10348 (P : ℝ) (hP : P = 2000) (r : ℝ) (hr : r = 0.05) (t : ℕ) (ht : t = 18) :
    round (P * (1 + r) ^ t * 100) / (100 : ℝ) = 4813.24 := by 
  rw [hP, hr, ht]
  norm_num [round_eq]