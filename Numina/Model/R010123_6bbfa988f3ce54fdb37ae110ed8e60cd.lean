import Mathlib
theorem algebra_3728 {n : ℕ} (hn : n = 48) :
    62 * 4 + 20 * n = 1208 := by
  subst hn
  all_goals norm_num