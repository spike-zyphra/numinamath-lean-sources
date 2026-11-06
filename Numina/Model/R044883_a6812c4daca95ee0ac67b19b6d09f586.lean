import Mathlib

theorem algebra_19359 {f : ℝ → ℝ} (h : f ≠ 0) (h' : 8 = 1 / 4 * f (1 / 2 * 8)) :
    32 = f 4 ∧ 32 + 4 = 36 := by 
  have eq1 : f 4 = 32 := by
    norm_num at h'
    linarith
  constructor
  · -- Show that 32 = f 4
    linarith [eq1]
  · -- Show that 32 + 4 = 36
    norm_num