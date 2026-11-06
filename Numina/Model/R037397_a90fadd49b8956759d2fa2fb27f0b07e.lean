import Mathlib

theorem inequalities_57844 (x1 x2 y1 y2 : ℝ)
    (h : x1^2 + x2^2 ≤ 1) :
    (x1 * y1 + x2 * y2 - 1)^2 ≥ (x1^2 + x2^2 - 1) * (y1^2 + y2^2 - 1) := by
  nlinarith [sq_nonneg (x1 * y2 - x2 * y1), sq_nonneg (x1 - y1), sq_nonneg (x2 - y2),
          sq_nonneg (x1 * y1 + x2 * y2 - (x1^2 + x2^2)), sq_nonneg (x1 * y1 + x2 * y2 - (y1^2 + y2^2)), 
          sq_nonneg (x1 + y1), sq_nonneg (x2 + y2), 
          sq_nonneg (x1 * y2 - x2 * y1), 
          mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 1 - x1^2 - x2^2 by nlinarith)]