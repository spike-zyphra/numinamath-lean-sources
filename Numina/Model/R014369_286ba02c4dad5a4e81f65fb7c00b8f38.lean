import Mathlib

theorem algebra_292094 (x : Fin 3 → ℝ)
    (h1 : x 0 + (1 / 2) * x 1 + (1 / 3) * x 2 = 1)
    (h2 : x 0 ^ 2 + (1 / 2) * x 1 ^ 2 + (1 / 3) * x 2 ^ 2 = 3) :
    x 2 ≥ -21 / 11 := by
  nlinarith [sq_nonneg (x 0 - 12 / 11), sq_nonneg (x 1 - 18 / 11), sq_nonneg (x 2 + 21 / 11),
            sq_nonneg (x 0 - (x 1 / 2)), sq_nonneg (x 0 - ((14 / 11) * x 2 / 9)), sq_nonneg (x 1 - ((14 / 11) * x 2 / 6)), sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]