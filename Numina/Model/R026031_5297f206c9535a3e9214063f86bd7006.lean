import Mathlib

theorem algebra_128659 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : x^3 + y^3 = x^2 + 42 * x * y + y^2) :
    (x = 1 ∧ y = 7) ∨ (x = 7 ∧ y = 1) ∨ (x = 22 ∧ y = 22) := by
  have h1 : x ≤ 44 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 44), sq_nonneg (x - 22), sq_nonneg (y - 22),
      sq_nonneg (x - y), sq_nonneg (x + y - 44)]
  have h2 : y ≤ 44 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 44), sq_nonneg (x - 22), sq_nonneg (y - 22),
      sq_nonneg (x - y), sq_nonneg (x + y - 44)]
  interval_cases x <;> interval_cases y
    <;> omega