import Mathlib

theorem algebra_5015 (x : ℝ) (h : 1.5 / 100 * x = 60) : x = 4000 := by
  have h1 : x = 4000 := by
    norm_num at h
    linarith
  exact h1