import Mathlib

theorem other_151930 (d : ℝ) (h : d > 0) (h1 : 3 * v1 = d - 3 * v2) (h2 : 3 * v2 = d - 3 * v1 - 15) :
    d / v2 = 7.2 := by
  have eq1 : 3 * v1 + 3 * v2 = d := by
    linarith
  have eq2 : 3 * v1 + 3 * v2 + 15 = d := by
    linarith
  have h3 : (15 : ℝ) = (0 : ℝ) := by
    linarith [eq1, eq2]
  nlinarith