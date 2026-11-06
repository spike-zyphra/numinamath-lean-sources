import Mathlib

theorem algebra_182716 {x : ℝ} (hx : x > 0) (h : 20 * x = 12 * 10 ^ 6 + 7.8 * 10 ^ 3 * x) :
    x = 8.721 := by
  ring_nf at h
  linarith