import Mathlib

theorem algebra_224383 (d : ℝ) (h : d > 0) (h1 : 70 / d = (d - 70) / (d - 90)) :
    d = 120 := by
  have h2 : d ≠ 0 := by linarith
  have h3 : d - 90 ≠ 0 := by
    by_contra h4
    have h5 : d = 90 := by linarith
    rw [h5] at h1
    norm_num at h1 <;> all_goals linarith
  field_simp [h2, h3] at h1
  nlinarith [sq_nonneg (d - 70), sq_nonneg (d - 90)]