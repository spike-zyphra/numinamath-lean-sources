import Mathlib

theorem inequalities_603577 (x1 x2 x3 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) :
    x1 * x2 * x3 ≥ (x2 + x3 - x1) * (x1 + x3 - x2) * (x1 + x2 - x3) := by 
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x2 - x3), 
          sq_nonneg (x1 + x2 - x3), sq_nonneg (x1 - x2 + x3), sq_nonneg (-x1 + x2 + x3),
          mul_pos hx1 hx2, mul_pos hx1 hx3, mul_pos hx2 hx3
         ]