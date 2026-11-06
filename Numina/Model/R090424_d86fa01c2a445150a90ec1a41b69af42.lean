import Mathlib

theorem algebra_97530 {x1 x2 h b : ℝ} (hne : x1 ≠ x2) (h1 : 3 * x1 ^ 2 - h * x1 = b) (h2 : 3 * x2 ^ 2 - h * x2 = b) :
    x1 + x2 = h / 3 := by
  have eq1 : 3 * x1 ^ 2 - h * x1 - (3 * x2 ^ 2 - h * x2) = 0 := by
    linarith [h1, h2]
  have eq2 : (x1 - x2) * (3 * (x1 + x2) - h) = 0 := by
    linarith [eq1]
    <;> nlinarith
  cases (mul_eq_zero.mp eq2) with
  | inl h3 =>
    exfalso
    exact hne (by linarith)
  | inr h4 =>
    linarith