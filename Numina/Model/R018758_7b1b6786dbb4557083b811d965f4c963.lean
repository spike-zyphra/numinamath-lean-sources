import Mathlib

theorem inequalities_601860 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a^3 + b^3 ≥ Real.sqrt (a * b) * (a^2 + b^2) := by 
  nlinarith [sq_nonneg (a^3 - b^3), sq_nonneg (a - b), sq_nonneg (a^2 - b^2), 
          sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
          sq_nonneg (Real.sqrt (a * b) - a), sq_nonneg (Real.sqrt (a * b) - b), 
          Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), 
          sq_nonneg (a - b), sq_nonneg (a^2 - b^2), 
          mul_nonneg ha hb]