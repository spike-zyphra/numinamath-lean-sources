import Mathlib

theorem algebra_100965 {v u : ℝ} (h : v > 0) (hu : u > 0)
    (h1 : 6 * u = 2 * 13.5 * v) (h2 : 13.5 * u = 2 * 6 * v) :
    6 * u = 324 * v := by 
  nlinarith