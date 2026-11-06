import Mathlib

theorem algebra_321486 {x y : ℝ} (h : (x + Real.sqrt (y^2 + 1)) * (y + Real.sqrt (x^2 + 1)) = 1) :
    x + y = 0 := by
  have h1 : 0 < Real.sqrt (y ^ 2 + 1) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg y]
  have h2 : 0 < Real.sqrt (x ^ 2 + 1) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg x]
  have h3 : (x + Real.sqrt (y^2 + 1)) * (y + Real.sqrt (x^2 + 1)) = 1 := h
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1),
          sq_nonneg (Real.sqrt (y ^ 2 + 1) - Real.sqrt (x ^ 2 + 1)), 
          Real.sqrt_nonneg (y ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 + 1),
          mul_nonneg (Real.sqrt_nonneg (y ^ 2 + 1)) (Real.sqrt_nonneg (x ^ 2 + 1)),
          Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by nlinarith),
          Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith),
          mul_self_nonneg (x + y), mul_self_nonneg (x - y)]