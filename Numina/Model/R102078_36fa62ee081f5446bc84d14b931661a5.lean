import Mathlib

theorem algebra_254 (d m a : ℝ) (hd : d > 0) (h1 : m = (2 * d - 400) / 3) (h2 : a = d - m) (h3 : 2 * a = d - 2 * m) : d = 600 := by
    rw [h2] at h3
    linarith [h1, h3]