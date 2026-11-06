import Mathlib

theorem algebra_188413 (d : ℝ) (h : d > 0) (h1 : 4 / d = 15 / (d - 4)) :
    d = 20 := by
  have h2 : d - 4 ≠ 0 := by
    by_contra h3
    have h4 : d = 4 := by linarith
    rw [h4] at h1
    norm_num at h1
    all_goals linarith
  have h3 : d ≠ 0 := by linarith
  field_simp [h3, h2] at h1
  nlinarith