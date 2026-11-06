import Mathlib

theorem algebra_319843 {x : ℝ} (hx : x^3 - x^2 + x - 2 = 0) :
    x^4 + 2 * x^3 - 2 * x^2 + x - 1 = 5 := by
  have h1 : x^3 = x^2 - x + 2 := by
    linarith
  have h3 : x^4 = x + 2 := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (x^2 - x + 2) := by rw [h1]
      _ = x^3 - x^2 + 2 * x := by ring
      _ = (x^2 - x + 2) - x^2 + 2 * x := by rw [h1]
      _ = x + 2 := by ring
  rw [h3]
  rw [show x^3 = x^2 - x + 2 by linarith [hx]]
  ring
  <;> nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x - 2)]