import Mathlib

theorem algebra_21325 (n : ℕ) (h : n > 0) (h' : n + (n + 1) + (n + 2) = 1341) :
    max (max n (n + 1)) (n + 2) = 448 := by
  have hn : n = 446 := by
    omega
  rw [hn]
  all_goals norm_num