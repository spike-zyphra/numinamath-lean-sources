import Mathlib

theorem algebra_124150 (d : ℝ) (h : d > 0) (h1 : 100 / d = 300 / (d - 100)) :
    d = 600 := by
  have h2 : d ≠ 0 := by linarith
  have h3 : d - 100 ≠ 0 := by
    by_contra h4
    have h4' : d = 100 := by linarith
    rw [h4'] at h1
    norm_num at h1
    all_goals linarith
  field_simp [h2, h3] at h1
  nlinarith