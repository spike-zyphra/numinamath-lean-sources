import Mathlib

theorem algebra_24761 (v1 v2 : ℝ) (h1 : v1 > 0) (h2 : v2 > 0)
    (h3 : v1 * 35 + v2 * 45 = 20) (h4 : v1 * 55 + v2 * 35 = 15) :
    v1 * 12 + v2 * 12 = 13 := by 
  linarith