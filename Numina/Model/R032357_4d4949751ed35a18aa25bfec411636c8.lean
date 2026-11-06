import Mathlib

theorem algebra_95410 {n : ℤ} (h : 3 * n = 4 * (n - 4)) :
3 * n = 48 := by 
  have eq1 : 3 * n = 4 * n - 16 := by
    linarith [h]
  have eq2 : n = 16 := by
    linarith [eq1]
  have eq3 : 3 * n = 48 := by
    rw [eq2]
    all_goals norm_num 
  exact_mod_cast eq3