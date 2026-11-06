import Mathlib

theorem algebra_121912 {x : ℝ} (hx : x * (x + 3) = 154) : (x + 1) * (x + 2) = 156 := by 
  have h1 : x ^ 2 + 3 * x = 154 := by
    linarith [hx]
  have h2 : (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by
    ring
  rw [h2]
  linarith [h1]