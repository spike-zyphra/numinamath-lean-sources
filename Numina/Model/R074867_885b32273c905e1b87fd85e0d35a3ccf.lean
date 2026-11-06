import Mathlib

theorem algebra_3931 {k : ℝ} (h : k ^ 2 + 3 * k = 5) : k ^ 4 + 11 * k ^ 3 + 36 * k ^ 2 + 11 * k + 1 = 86 := by
  have h1 : k ^ 2 = 5 - 3 * k := by linarith
  have h2 : k ^ 3 = 14 * k - 15 := by 
    calc 
      k ^ 3 = k * (k ^ 2) := by ring
      _ = k * (5 - 3 * k) := by rw [h1]
      _ = 5 * k - 3 * (k ^ 2) := by ring
      _ = 5 * k - 3 * (5 - 3 * k) := by rw [h1]
      _ = 14 * k - 15 := by ring
  have h3 : k ^ 4 = 70 - 57 * k := by 
    calc 
      k ^ 4 = k * (k ^ 3) := by ring
      _ = k * (14 * k - 15) := by rw [h2]
      _ = 14 * (k ^ 2) - 15 * k := by ring
      _ = 14 * (5 - 3 * k) - 15 * k := by rw [h1]
      _ = 70 - 57 * k := by ring
  rw [h3, h2, h1]
  ring