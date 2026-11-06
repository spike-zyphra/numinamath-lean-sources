import Mathlib

theorem algebra_191896 (v1 v2 : ℝ) (h1 : v1 > 0) (h2 : v2 > 0)
    (h3 : (1 / 60) * (v1 * (1 - 1 / 60) + v2 * (1 + 30 / 60)) = 18 / 60)
    (h4 : (1 / 60) * (v1 * (1 + 30 / 60) + v2 * (1 - 1 / 60)) = 11200 / 60) :
    v1 = 16 ∧ v2 = 14 := by
  constructor
  all_goals
    linarith