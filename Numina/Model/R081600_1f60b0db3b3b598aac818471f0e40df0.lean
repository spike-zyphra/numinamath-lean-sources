import Mathlib

theorem algebra_1320 {x : ℝ} (hx : 2 * x ^ 2 - x = 1) : 4 * x ^ 4 - 4 * x ^ 3 + 3 * x ^ 2 - x - 1 = 1 := by
  have h1 : x ^ 2 = (x + 1) / 2 := by
    linarith
  have h2 : x ^ 3 = (3 * x + 1) / 4 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * ((x + 1) / 2) := by rw [h1]
      _ = (x * (x + 1)) / 2 := by ring
      _ = (x^2 + x) / 2 := by ring
      _ = ((x + 1)/2 + x) / 2 := by rw [h1]
      _ = (3 * x + 1) / 4 := by ring
  have h3 : x ^ 4 = (5 * x + 3) / 8 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = ((x + 1) / 2) ^ 2 := by rw [h1]
      _ = ((x + 1) ^ 2) / 4 := by ring
      _ = (x ^ 2 + 2 * x + 1) / 4 := by ring
      _ = ((x + 1)/2 + 2 * x + 1) / 4 := by rw [h1]
      _ = (5 * x + 3) / 8 := by
        linarith
  have eq1 : 4 * x ^ 4 - 4 * x ^ 3 + 3 * x ^ 2 - x - 1 = 1 := by
    rw [show x ^ 4 = (5 * x + 3) / 8 by linarith [h3]]
    rw [show x ^ 3 = (3 * x + 1) / 4 by linarith [h2]]
    rw [show x ^ 2 = (x + 1) / 2 by linarith [h1]]
    linarith
  linarith [eq1]