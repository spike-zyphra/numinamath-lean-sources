import Mathlib

theorem algebra_232205 {x : ℝ} (hx : x^2 - x - 100 = 0) : x^4 - 201 * x = 10100 := by
  have h1 : x^2 = x + 100 := by
    linarith

  have h3 : x^4 = 201 * x + 10100 := by
    calc
      x^4 = (x^2)^2 := by ring
      _ = (x + 100)^2 := by rw [h1]
      _ = x^2 + 200 * x + 10000 := by ring
      _ = (x + 100) + 200 * x + 10000 := by rw [h1]
      _ = 201 * x + 10100 := by ring

  rw [h3]
  all_goals linarith