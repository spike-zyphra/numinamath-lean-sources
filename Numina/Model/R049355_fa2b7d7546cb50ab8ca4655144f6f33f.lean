import Mathlib

theorem algebra_219366 (v1 v2 : ℝ) (h1 : v1 = 2 * v2) (h2 : v1 * 45 = v2 * 16) :
    v1 * 10 = v2 * 13 := by
  rw [h1] at h2
  linarith