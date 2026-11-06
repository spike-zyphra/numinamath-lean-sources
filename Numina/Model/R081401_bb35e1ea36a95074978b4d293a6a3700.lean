import Mathlib

theorem algebra_294660 (x : ℝ) (hx : x^2 + abs x + 1 = 0) :
    x^2 + (x + abs x) + 1 = 0 ↔ x^2 + (x + abs x) + 1 = -(3 + Real.sqrt 5) := by
  have h1 : x^2 + abs x + 1 > 0 := by
    cases abs_cases x with
    | inl h =>
      nlinarith [sq_nonneg (x), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2)]
    | inr h =>
      nlinarith [sq_nonneg (x), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2)]
  linarith