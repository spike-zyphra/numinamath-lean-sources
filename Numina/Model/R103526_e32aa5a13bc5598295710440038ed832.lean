import Mathlib

theorem algebra_200536 (v : ℝ) (h : v > 0) (h1 : 5 * v = 1800) (h2 : 15 * (1.5 * v) = 320 * (17 - 5)) :
    v = 72 := by
  nlinarith