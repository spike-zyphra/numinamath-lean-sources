import Mathlib

theorem inequalities_320619 (x y : ℝ) (h : x^5 + y^5 = 2) : x + y ≤ 2 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), 
            sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (x + y - 2), 
            sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1),
            sq_nonneg (x^2), sq_nonneg (y^2), 
            sq_nonneg (x^2 - y^2), sq_nonneg (x * y -1),
            sq_nonneg (x + y - 2)
          ]