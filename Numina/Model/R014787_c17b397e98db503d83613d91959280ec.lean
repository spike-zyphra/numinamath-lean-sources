import Mathlib

theorem algebra_161810 (α β : ℝ) :
    (2 * Real.cos α + 5 * Real.sin β - 8)^2 + (2 * Real.sin α + 5 * Real.cos β - 15)^2 ≥ 100 := by
  nlinarith [sq_nonneg (2 * Real.cos α + 5 * Real.sin β - 56 / 17), sq_nonneg (2 * Real.sin α + 5 * Real.cos β - 105 / 17), 
          sq_nonneg (Real.cos α - 8 / 17), sq_nonneg (Real.sin α - 15 / 17), 
          sq_nonneg (Real.sin β - 8 / 17), sq_nonneg (Real.cos β - 15 / 17), 
          Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, 
          sq_nonneg (Real.sin β - Real.cos α), sq_nonneg (Real.sin α - Real.cos β), 
          mul_self_nonneg (Real.sin β - Real.sin α), mul_self_nonneg (Real.cos β - Real.cos α)]