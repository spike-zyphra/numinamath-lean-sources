import Mathlib

theorem algebra_179584 (p : ℝ) (hp : p^3 + p - 3 = 0) :
    (p^2)^3 + 2 * (p^2)^2 + (p^2) - 9 = 0 := by

  have h1 : p^3 = 3 - p := by linarith

  have h2 : p^4 = 3 * p - p^2 := by
    calc
      p^4 = p * p^3 := by ring
      _ = p * (3 - p) := by rw [h1]
      _ = 3 * p - p^2 := by ring

  have h3 : p^6 = 9 - 6 * p + p^2 := by
    calc
      p^6 = (p^3)^2 := by ring
      _ = (3 - p)^2 := by rw [h1]
      _ = 9 - 6 * p + p^2 := by ring

  calc
    (p^2)^3 + 2 * (p^2)^2 + (p^2) - 9
      = p^6 + 2 * p^4 + p^2 - 9 := by
        ring
    _ = (9 - 6 * p + p^2) + 2 * (3 * p - p^2) + p^2 - 9 := by
      rw [h3, h2]
    _ = 0 := by
      ring