import Mathlib

theorem algebra_724 (v : ℝ) (h : v = 50) :
    (v * (60 / 5)) / (1 + (2 / 60) * (60 / 5)) = (50 * 60 / 5) / (1 + 2 / 60 * (60 / 5)) := by 
  rw [h]
  all_goals ring_nf <;> norm_num