import Mathlib

theorem algebra_93632 (x p : ℝ) (hx : x < 2) (h : abs (x - 2) = p) : x - p = 2 - 2 * p := by
  have h1 : x - 2 < 0 := by linarith
  rw [abs_of_neg h1] at h
  linarith