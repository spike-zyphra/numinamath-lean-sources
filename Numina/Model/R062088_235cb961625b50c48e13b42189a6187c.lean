import Mathlib

theorem algebra_4393 (v c : ℝ) (h : v > 0) (h1 : c > 0)
    (h2 : 6 * v = 10 * c) (h3 : 10 * v = 15 * c + 6 * 24) (h4 : 15 * v = 10 * c + 6 * 20) :
    v = 18 := by
  linarith