import Mathlib

theorem algebra_315105 {x y : ℝ} (hx : (x - 1)^3 + 1998 * (x - 1) = -1) (hy : (y - 1)^3 + 1998 * (y - 1) = 1) : x + y = 2 := by
  have eq1 : (x - 1)^3 + 1998 * (x - 1) + (y - 1)^3 + 1998 * (y - 1) = 0 := by
    linarith
  have eq2 : (x - 1 + y - 1) * ((x - 1)^2 - (x - 1) * (y - 1) + (y - 1)^2 + 1998) = 0 := by
    nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1))]
  cases' (mul_eq_zero.mp eq2) with h1 h2
  · -- When $h1$ holds: $x - 1 + y - 1 = 0$, which implies $x + y - 2 = 0$
    linarith 
  · -- Show second part to be contradiction
    nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg (x - 1 - (y - 1)), sq_nonneg (x - 1 + (y - 1)), sq_nonneg (x - 1 - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg (x - 1 - (y - 1))]