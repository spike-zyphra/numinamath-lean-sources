import Mathlib

theorem algebra_127331 (v : ℝ) (h : v > 0) (h1 : 9.25 * v = 9.15 * (v + w)) (h2 : 9.75 * v = 9.15 * (v - w)) :
    (9.3 : ℝ) * v = 9.15 * (v + w) := by
  have h3 : 9.15 * (v + w) = 9.25 * v := by linarith [h1]
  nlinarith [h3, h, h2]