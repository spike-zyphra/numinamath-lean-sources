import Mathlib

theorem algebra_21784 {x : ℝ} (hx : x > 0) (h : (4 ^ 2) / (x ^ 2) = 4 / 9) :
    x = 6 := by
  have h1 : x^2 > 0 := by nlinarith [sq_pos_of_pos hx]
  field_simp at h
  nlinarith [sq_nonneg (x - 6), sq_nonneg (x + 6), h1]