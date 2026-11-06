import Mathlib

theorem algebra_114803 {x y : ℝ}
  (hx : (x - 1)^3 + 1997 * (x - 1) = -1) (hy : (y - 1)^3 + 1997 * (y - 1) = 1) :
  x + y = 2 := by
  have h : (x - 1) ^ 3 + 1997 * (x - 1) + (y - 1) ^ 3 + 1997 * (y - 1) = 0 := by
    linarith [hx, hy]

  have h1 : (x - 1 + y - 1) * ((x - 1) ^ 2 - (x - 1) * (y - 1) + (y - 1) ^ 2 + 1997) = 0 := by
    nlinarith [h]

  cases' (mul_eq_zero.1 h1) with h2 h3

  · -- Case $x - 1 + y - 1 = 0$
    linarith

  · -- Case $(x - 1) ^ 2 - (x - 1) * (y - 1) + (y - 1) ^ 2 + 1997 = 0$
    have h4 : (x - 1) ^ 2 - (x - 1) * (y - 1) + (y - 1) ^ 2 + 1997 = 0 := by
      linarith
    have h5 : (x - 1) ^ 2 - (x - 1) * (y - 1) + (y - 1) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1))]
    have h6 : (x - 1) ^ 2 - (x - 1) * (y - 1) + (y - 1) ^ 2 = -1997 := by
      linarith [h4]
    linarith [h6, h5]