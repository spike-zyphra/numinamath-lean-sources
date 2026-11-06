import Mathlib

theorem algebra_281039 {x : ℝ} (hx : x > 0) (h : 5 * x * (x / 2) = 160) :
    x = 8 := by

  have h1 : 5 * x ^ 2 = 320 := by
    linarith

  have h2 : x ^ 2 = 64 := by
    nlinarith

  have h3 : x = 8 := by
    nlinarith [sq_nonneg x, h2]

  exact h3