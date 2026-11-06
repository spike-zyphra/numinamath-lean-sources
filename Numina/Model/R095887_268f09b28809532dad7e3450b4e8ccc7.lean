import Mathlib

theorem algebra_221031 (d t : ℝ) (ht : t = 40 - 6) (h : d/t = 30 ∧ d/(t+6) = 50) :
    d/(t+6) = 10 := by
  have ht' : t = 34 := by linarith
  rw [ht'] at h ⊢
  norm_num at h ⊢
  all_goals linarith