import Mathlib

theorem algebra_161135 (d : ℝ) (h : d = 189) (h1 : 54 / d = 15 / 60) :
    (9.15 - 8.3) / 60 = 10.08 := by
  rw [h] at h1
  norm_num at h1
  all_goals norm_num at h1 ⊢ <;> try linarith
  all_goals linarith