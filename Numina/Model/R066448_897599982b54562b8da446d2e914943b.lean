import Mathlib

theorem algebra_51024 {x : ℝ} {a : ℕ → ℝ} (h1 : x^4 + a 1 * x^3 + a 2 * x^2 + a 3 * x + a 4 = 0)
    (h2 : 4 * x^3 + 3 * a 1 * x^2 + 2 * a 2 * x + a 3 = 0) :
    (X - x)^2 ∣ X^4 + a 1 * X^3 + a 2 * X^2 + a 3 * X + a 4 := by 
  use X^2 + (a 1 + 2 * x) * X + (a 2 + 2 * x * a 1 + 3 * x^2)
  have ha4 : a 4 = - (x^4 + a 1 * x^3 + a 2 * x^2 + a 3 * x) := by linarith [h1]
  have ha3 : a 3 = -4 * x^3 - 3 * a 1 * x^2 - 2 * a 2 * x := by linarith [h2]
  rw [ha4, ha3]
  ring_nf
  <;> nlinarith