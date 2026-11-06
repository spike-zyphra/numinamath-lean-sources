import Mathlib

theorem algebra_271637 (t r : ℝ) (ht : t > 0) (hr : r > 0)
    (h : r = 5 * t) (h1 : t * 1000 = r * 990 + 10) :
    t * 802 = r * 1000 := by
  rw [h] at h1
  nlinarith