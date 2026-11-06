import Mathlib

theorem algebra_230316 {x y : ℚ} (h : x + y = 1) :
    x - y = (x ^ 2 - y ^ 2) := by
  have h1 : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
    ring
  rw [h] at h1
  linarith