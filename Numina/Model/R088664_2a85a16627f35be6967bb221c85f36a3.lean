import Mathlib

theorem algebra_128486 (v : ℝ) (h : v > 0) (h1 : 40 * v = 45 * (v + 5)) (h2 : 40 * (v + 10) = 45 * v) :
    v = 60 := by
      linarith