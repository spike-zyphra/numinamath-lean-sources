import Mathlib

theorem algebra_6952 {m : ℝ} (h : m = (4 - 7) / (2 - (-1))) :
    ∀ x, m * x + 6 = -x + 6 := by
  have hm : m = -1 := by
    rw [h]
    norm_num
  intro x
  rw [hm]
  all_goals ring