import Mathlib

theorem algebra_13977 (x : ℝ) (hx : x ^ 3 + 4 * x = 8) : x ^ 7 + 64 * x ^ 2 = 128 := by
  have h1 : x ^ 3 = 8 - 4 * x := by linarith
  have h2 : x ^ 4 = 8 * x - 4 * x ^ 2 := by
    calc
      x ^ 4 = x * x ^ 3 := by ring
      _ = x * (8 - 4 * x) := by rw [h1]
      _ = 8 * x - 4 * x ^ 2 := by ring
  have h3 : x ^ 5 = 8 * x ^ 2 + 16 * x - 32 := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ = x * (8 * x - 4 * x ^ 2) := by rw [h2]
      _ = 8 * x ^ 2 - 4 * x ^ 3 := by ring
      _ = 8 * x ^ 2 - 4 * (8 - 4 * x) := by rw [h1]
      _ = 8 * x ^ 2 + 16 * x - 32 := by ring
  have h4 : x ^ 6 = 64 - 64 * x + 16 * x ^ 2 := by
    calc
      x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ = (8 - 4 * x) ^ 2 := by rw [h1]
      _ = 64 - 64 * x + 16 * x ^ 2 := by ring
  have h5 : x ^ 7 = -64 * x ^ 2 + 128 := by
    calc
      x ^ 7 = x * x ^ 6 := by ring
      _ = x * (64 - 64 * x + 16 * x ^ 2) := by rw [h4]
      _ = 64 * x - 64 * x ^ 2 + 16 * x ^ 3 := by ring
      _ = 64 * x - 64 * x ^ 2 + 16 * (8 - 4 * x) := by rw [h1]
      _ = -64 * x ^ 2 + 128 := by ring
  linarith [h5]