import Mathlib

theorem algebra_304972 (a b : ℝ) (ha : 0 < b) (h : a ≥ b)
    (h1 : a * (Real.sin α)^2 + b * Real.sin α - b = 0) :
    Real.sin α ≤ (Real.sqrt 5 - 1) / 2 := by
  have h5 : a * (Real.sin α)^2 = b * (1 - Real.sin α) := by
    nlinarith
  have h8 : Real.sin α ^ 2 + Real.sin α - 1 ≤ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (Real.sin α), sq_nonneg (a * (Real.sin α)^2 - b * (1 - Real.sin α)), 
          h5, h, ha, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), h8]