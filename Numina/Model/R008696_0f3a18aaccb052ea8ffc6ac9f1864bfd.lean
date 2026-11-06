import Mathlib

theorem algebra_14205 {x : ℝ} (h : 5 * x ^ 2 + 4 = 3 * x + 9) : (10 * x - 3) ^ 2 = 109 := by
  have h1 : 5 * x^2 - 3 * x - 5 = 0 := by linarith
  have h2 : 5 * x^2 = 3 * x + 5 := by linarith [h1]
  calc
    (10 * x - 3) ^ 2 = 100 * x^2 - 60 * x + 9 := by ring
    _ = (60 * x + 100) - 60 * x + 9 := by
      have h3 : 100 * x^2 = 60 * x + 100 := by
        linarith [h2]
      linarith [h3]
    _ = 109 := by linarith