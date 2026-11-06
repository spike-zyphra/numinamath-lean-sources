import Mathlib

theorem algebra_186264 {x : ℝ} (hx : x^3 + x^2 + x + 1 = 0) :
    x^4 + 2 * x^3 + 2 * x^2 + 2 * x + 1 = 0 := by
  have h1 : x^3 = -x^2 - x - 1 := by
    linarith 
  have h2 : x^4 = -x^3 - x^2 - x := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (-x^2 - x - 1) := by rw [h1]
      _ = -x^3 - x^2 - x := by ring 
  calc
    x^4 + 2 * x^3 + 2 * x^2 + 2 * x + 1 
        = (-x^3 - x^2 - x) + 2 * x^3 + 2 * x^2 + 2 * x + 1 := by
          rw [h2]
    _ = (x^3 + x^2 + x + 1) := by ring
    _ = 0 := by
      linarith [hx]