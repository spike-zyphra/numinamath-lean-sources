import Mathlib

theorem algebra_212811 {x : ℝ} {a : ℕ → ℝ} (hx : x^4 + a 1 * x^3 + a 2 * x^2 + a 3 * x + a 4 = 0)
    (h4x : 4 * x^3 + 3 * a 1 * x^2 + 2 * a 2 * x + a 3 = 0) :
    (X - x)^2 ∣ X^4 + a 1 * X^3 + a 2 * X^2 + a 3 * X + a 4 := by
  use (X^2 + (a 1 + 2 * x) * X + (a 2 + 2 * x * (a 1) + 3 * x ^ 2))
  have ha3 : a 3 = -4 * x ^ 3 - 3 * (a 1) * x ^ 2 - 2 * (a 2) * x := by
    linarith [h4x]
  have ha4 : a 4 = 3 * x ^ 4 + 2 * (a 1) * x ^ 3 + (a 2) * x ^ 2 := by
    have ha3' : a 3 = -4 * x ^ 3 - 3 * (a 1) * x ^ 2 - 2 * (a 2) * x := by
      linarith [h4x]
    have ha4 : a 4 = -x ^ 4 - (a 1) * x ^ 3 - (a 2) * x ^ 2 - (a 3) * x := by
      linarith [hx]
    rw [ha3'] at ha4
    nlinarith
  rw [ha3, ha4]
  ring