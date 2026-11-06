import Mathlib

theorem algebra_162603 (t : ℝ) (ht : t > 0) (h1 : 60 * t = 3 * (60 * (t - 7 / 60))) (h2 : 60 * (t + 7 / 60) = 2 * (60 * t)) :
    t = 11 := by
  nlinarith