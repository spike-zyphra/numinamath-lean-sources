import Mathlib

theorem algebra_15619 {n : ℕ} (hn : n = 52) :
    n * (n - 1) = 2652 := by 
  subst hn
  all_goals norm_num