import Mathlib

theorem other_129005 (d : ℝ) (h : d > 0) (h1 : 3 / d = 3.25 / (d - 1)) (h2 : d / 2 ≤ 4) :
    d = 1.5 := by
  have h3 : d - 1 ≠ 0 := by
    by_contra h4
    have h5 : d = 1 := by linarith
    rw [h5] at h1
    norm_num at h1
  have h4 : d ≠ 0 := by linarith
  field_simp [h4, h3] at h1
  nlinarith