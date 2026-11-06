import Mathlib

theorem algebra_163353 (v : ℝ) (h : v > 0) (h1 : 6 * v = 8 * (v + w)) (h2 : 8 * (v + w) = 5 * (v + 2 * w)) :
    12 * v = 12 * (v + w) + 1 / 3 := by
  nlinarith