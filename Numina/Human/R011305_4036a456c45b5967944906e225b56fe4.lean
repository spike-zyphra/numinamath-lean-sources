import Mathlib

  theorem algebra_2842 (a : ℝ) (x : ℝ) (h : x = 2) (h1 : (1/9) * ((1/6) * ((1/3) * ((x + a)/2 + 4) - 7) + 10) = 1) : a = -4 := by
    rw [h] at h1
    linarith