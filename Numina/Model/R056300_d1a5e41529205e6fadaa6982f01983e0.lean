import Mathlib

theorem algebra_254024 {x : ℝ} (hx : x > 0) (h : 12 * x + 10 * x = 12 * (x * (1 - 2 / 100)) + 10 * (x * (1 + 10 / 100))) :
    (12 * (x * (1 - 2 / 100)) + 10 * (x * (1 + 10 / 100))) / (12 * x + 10 * x) = 1.04 := by
  ring_nf at h
  nlinarith