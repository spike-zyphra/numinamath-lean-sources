import Mathlib

theorem algebra_229360 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : v1 = 2 * v2) (h2 : v2 * 10 = v1 * 15 + 4) :
    v2 = 72 := by
  rw [h1] at h2
  nlinarith