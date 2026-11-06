import Mathlib

theorem algebra_265789 (x : Fin 4 → ℝ) (h : 5 * x 0 + 6 * x 1 - 7 * x 2 + 4 * x 3 = 1) :
    3 * (x 0)^2 + 2 * (x 1)^2 + 5 * (x 2)^2 + (x 3)^2 ≥ 15 / 782 := by 
  nlinarith [sq_nonneg (x 0 - 25 / 782), sq_nonneg (x 1 - 45 / 782), sq_nonneg (x 2 + 21 / 782), sq_nonneg (x 3 - 60 / 782),
            h]