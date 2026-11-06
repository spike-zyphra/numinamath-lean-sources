import Mathlib

theorem algebra_171829 (v : ℝ) (h : v > 0) (h1 : 5 / v = 9 / (v + 5)) (h2 : 5 / v = 6 / (v + 10)) :
    v = 27 := by
  have h1' : v ≠ 0 := by
    by_contra hv
    rw [hv] at h1
    norm_num at h1
  have h3 : v + 5 ≠ 0 := by
    by_contra hv
    have : v = -5 := by linarith
    rw [this] at h1
    norm_num at h1
  have h4 : v + 10 ≠ 0 := by
    by_contra hv
    have : v = -10 := by linarith
    rw [this] at h2
    norm_num at h2
  field_simp [h1', h3] at h1
  field_simp [h1', h4] at h2
  linarith