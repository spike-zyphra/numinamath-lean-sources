import Mathlib

theorem algebra_263101 (d : ℝ) (h : d > 0) (h1 : (15 / d) = (8 / (d - 15)) + 1 / 2) :
    d = 40 := by
  have h2 : d - 15 ≠ 0 := by
    by_contra h3
    have h4 : d = 15 := by linarith
    rw [h4] at h1
    norm_num at h1
  have h3 : d ≠ 0 := by linarith
  field_simp [h3, h2] at h1
  nlinarith [sq_nonneg (d - 40), sq_nonneg (d - 15 / 2), sq_pos_of_ne_zero (show d ≠ 0 by linarith), sq_pos_of_ne_zero (show d - 15 ≠ 0 by
    by_contra h3
    have h4 : d = 15 := by linarith
    rw [h4] at h1
    norm_num at h1
  )]