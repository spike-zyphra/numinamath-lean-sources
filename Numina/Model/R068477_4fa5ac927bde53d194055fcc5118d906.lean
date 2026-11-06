import Mathlib

theorem algebra_276059 (x y : ℝ) (hx : (x - 1)^3 + 1997 * (x - 1) = -1) (hy : (y - 1)^3 + 1997 * (y - 1) = 1) : x + y = 2 := by
  have eq1 : (x - 1)^3 + 1997 * (x - 1) + (y - 1)^3 + 1997 * (y - 1) = 0 := by
    linarith
  have eq2 : ((x - 1) + (y - 1)) * (( (x - 1) + (y - 1) )^2 - 3 * ((x - 1) * (y - 1)) + 1997) = 0 := by
    nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) * (y - 1)), sq_nonneg ((x - 1)^3), sq_nonneg ((y - 1)^3)]
  cases' (mul_eq_zero.mp eq2) with h1 h2
  · -- Case 1: $h1$ says $(x - 1) + (y - 1) = 0$ which implies $x + y = 2$
    linarith
  · -- Case 2: $h2$ says some quadratic expression equals zero, which will lead to a contradiction
    nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) * (y - 1)), sq_nonneg ((x - 1) - (y - 1) * 1997), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1)^2 - (y - 1)^2), sq_nonneg ((x - 1)^2 + (y - 1)^2)]