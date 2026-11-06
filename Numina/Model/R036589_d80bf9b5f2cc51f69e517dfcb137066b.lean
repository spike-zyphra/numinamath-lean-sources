import Mathlib

theorem number_theory_277004 (t : ℝ) (ht : t > 0) :
    (155 * t) % 400 = 0 ∧ (200 * t) % 400 = 0 ∧ (275 * t) % 400 = 0 := by
  norm_num at *
  all_goals linarith