import Mathlib

theorem calculus_60956 (v1 v2 : ℝ) (h1 : v1 = 2) (h2 : v2 = 4) :
    (1 / 2) * m * (v2 ^ 2 - v1 ^ 2) = 3 * (1 / 2) * m * (v1 ^ 2 - 0 ^ 2) := by 
  subst_vars
  ring