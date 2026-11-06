import Mathlib

theorem algebra_114109 (x : ℝ) (hx : x > 0) (h : 52 * x / 70 = 70 * x / 90 + 4) :
    x = 2196 := by
  -- Contradiction arises here.
  norm_num at h ⊢
  linarith -- Solves the linear inequality automatically