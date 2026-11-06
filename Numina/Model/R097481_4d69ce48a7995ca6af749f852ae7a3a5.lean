import Mathlib

theorem other_178304 {r : ℝ} (hr : r > 0) (h : (1 - r) / (1 - 256 * r) = 1 / 256) :
    r = 0.75 := by
  have h1 : 1 - 256 * r ≠ 0 := by
    by_contra h2
    rw [h2] at h
    norm_num at h
    all_goals linarith [h2]
  field_simp [h1] at h ⊢
  nlinarith