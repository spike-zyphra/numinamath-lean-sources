import Mathlib

theorem algebra_288911 (d t : ℝ) (ht : t > 0) (h1 : d / 20 = t - 30 / 60) (h2 : d / 12 = t + 30 / 60) :
    d / t = 15 := by 
  have eq1 : d = 20 * t - 10 := by
    linarith
  have eq2 : d = 12 * t + 6 := by
    linarith
  have ht2 : t = 2 := by
    linarith [eq1, eq2]
  have hd : d = 30 := by
    rw [ht2] at eq1
    linarith
  rw [hd, ht2]
  all_goals norm_num