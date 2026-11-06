import Mathlib

theorem algebra_222771 (x : ℝ) (hx : x > 0) (h : 30 / x = 40 / (x + 5)) :
    x = 15 := by
  have h1 : x ≠ 0 := by linarith
  have h2 : x + 5 ≠ 0 := by
    nlinarith
  field_simp [h1, h2] at h
  nlinarith [h, sq_pos_of_pos hx, sq_nonneg (x - 15)]