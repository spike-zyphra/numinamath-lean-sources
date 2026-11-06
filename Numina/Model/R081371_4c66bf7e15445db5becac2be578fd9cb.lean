import Mathlib

open Real

theorem calculus_2934 (x : ℝ) (hx : x > 0) (h : 3 / (2 - x) + 1 / x = 3 / 2 + 1 / 4) :
    x = 1 := by
  have h1 : x ≠ 0 := by linarith
  have h2 : 2 - x ≠ 0 := by
    by_contra h3
    have h4 : x = 2 := by linarith
    rw [h4] at h
    norm_num at h
  field_simp [h2, h1] at h
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 4 / 7)]