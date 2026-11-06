import Mathlib

theorem inequalities_139008 (x : ℝ) : (x^2 + 5) / Real.sqrt (x^2 + 4) > 2 := by
  have h1 : Real.sqrt (x^2 + 4) > 0 := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg x]
  have h4 : (x^2 + 5) > 2 * Real.sqrt (x^2 + 4) := by
    have h5 : (Real.sqrt (x^2 + 4)) ^ 2 = x ^ 2 + 4 := Real.sq_sqrt (by nlinarith [sq_nonneg x])
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (Real.sqrt (x ^ 2 + 4) - (x ^ 2 + 5) / 2), 
              h1, Real.sqrt_nonneg (x ^ 2 + 4), 
              Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 4 by nlinarith [sq_nonneg x]), 
              sq_nonneg (x ^ 2 + 3), 
              sq_nonneg (Real.sqrt (x ^ 2 + 4) ^ 2 - (x ^ 2 + 4))]
  have h6 : (x^2 + 5) / Real.sqrt (x^2 + 4) > 2 := by
    have h7 : Real.sqrt (x^2 + 4) > 0 := h1
    apply (lt_div_iff₀ h7).mpr
    linarith [h4]
  exact h6