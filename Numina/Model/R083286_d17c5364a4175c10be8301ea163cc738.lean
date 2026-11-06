import Mathlib

theorem algebra_0
  {x y : ℝ}
  (h1 : x^2 + x * y = 6)
  (h2 : x^2 + 5 * x * y - 4 * y^2 = 10) :
  x * y = 2 ∨ x * y = 3 / 2 := by
  have eq1 : x * y - y^2 = 1 := by
    nlinarith [h1, h2]
  have eq3 : (x * y - 2) * (x * y - 3 / 2) = 0 := by
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x - y / 2), sq_nonneg (x * y - y^2)]
  cases' (mul_eq_zero.mp eq3) with h4 h5
  · left
    linarith
  · right
    linarith