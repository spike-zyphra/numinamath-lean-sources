import Mathlib

theorem algebra_235492 {n : ℕ} (hn : n = 10^100) : 1000^100 = n^3 := by 
  rw [hn]
  all_goals norm_num