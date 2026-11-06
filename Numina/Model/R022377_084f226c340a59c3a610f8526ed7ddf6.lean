import Mathlib

theorem algebra_307530 (d : ℝ) (h : d > 0) (h1 : 10 / (d - 10) = 3 / d) :
    d = 27 := by
  have h2 : d - 10 ≠ 0 := by
    by_contra h2
    have h3 : d = 10 := by linarith
    rw [h3] at h1
    norm_num [h3] at h1
  have h3 : d ≠ 0 := by linarith
  have h4 : 10 * d = 3 * (d - 10) := by
    have h2' : d - 10 ≠ 0 := h2
    have h3' : d ≠ 0 := h3
    field_simp [h2', h3'] at h1 ⊢
    linarith
  have h5 : 7 * d = -30 := by
    nlinarith
  nlinarith