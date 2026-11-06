import Mathlib

theorem algebra_7952 (x : ℝ) (hx : 0 < x) (h : (1 + 30 / 100) * 200000 * (1 + x / 100) = 200000 * (1 + 4 / 100)) :
    x = 35.2 := by
  ring_nf at h
  nlinarith