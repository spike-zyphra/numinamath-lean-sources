import Mathlib

theorem algebra_170146 (d t : ℝ) (ht : t > 0) (h : d / t = 24) (h1 : d / (t + 20 / 60) = d / 2)
    (h2 : d / (t - 20 / 60) = d / 2 - 20) :
    d = 42 := by
  have h3 : t ≠ 0 := by linarith
  have h11 : d = 24 * t := by
    have : d / t = 24 := h
    field_simp [h3] at this ⊢
    linarith
  rw [show d = 24 * t by linarith [h11]] at h1 h2
  have h14 : t = 5 / 3 := by
    have h1' : (24 * t) / (t + 20 / 60) = (24 * t) / 2 := by
      linarith [h1]
    have h3' : t + 20 / 60 ≠ 0 := by
      by_contra h4
      have h4' : t + 20 / 60 = 0 := by linarith
      have h5' : t < 0 := by linarith
      linarith
    field_simp [h3'] at h1'
    nlinarith [sq_pos_of_pos ht]
  have h14' : (24 * t) / (t - 20 / 60) = (24 * t) / 2 - 20 := by
    linarith [h2]
  rw [show t = 5 / 3 by linarith [h14]] at h14'
  norm_num at h14'