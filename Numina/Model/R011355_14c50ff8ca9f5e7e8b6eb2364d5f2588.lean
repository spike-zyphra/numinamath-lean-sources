import Mathlib

theorem algebra_632 {x : ℝ} (hx : x ^ 2 - x - 1 = 0) : x ^ 3 - 2 * x + 1 = 2 := by
  have h1 : x ^ 2 = x + 1 := by
    linarith
  have h2 : x ^ 3 = 2 * x + 1 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * (x + 1) := by rw [h1]
      _ = x ^ 2 + x := by ring
      _ = (x + 1) + x := by rw [h1]
      _ = 2 * x + 1 := by ring
  calc
    x ^ 3 - 2 * x + 1 = (2 * x + 1) - 2 * x + 1 := by rw [h2]
    _ = 2 := by ring