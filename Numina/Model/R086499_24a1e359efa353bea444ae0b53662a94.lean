import Mathlib

theorem algebra_195421 (d : ℝ) (h : d > 0) (h1 : 15000 / d = 25000 / (d - 15000)) :
    d = 18750 := by
  have h2 : d ≠ 0 := by linarith
  have h3 : d - 15000 ≠ 0 := by
    by_contra h4
    have h5 : d = 15000 := by linarith
    rw [h5] at h1
    field_simp [h2, h5] at h1
    all_goals linarith
  field_simp [h2, h3] at h1
  nlinarith