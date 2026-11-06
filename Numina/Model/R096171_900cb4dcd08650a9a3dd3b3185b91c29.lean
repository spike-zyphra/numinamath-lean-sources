import Mathlib

open Real

theorem algebra_1443 (walk bus : ℝ) (h : bus + walk = 1.5) (h' : 2 * bus = 0.5) :
    2 * walk = 2.5 := by
  have h1 : bus = 0.25 := by
    linarith
  have h2 : walk = 1.25 := by
    linarith [h, h1]
  linarith [h2]